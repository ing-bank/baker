package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.actor.BakerActorProvider
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.{ActorBasedRecipeManager, RecipeManager}
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.{Config, ConfigFactory}
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import org.http4s.metrics.MetricsOps
import org.http4s.metrics.prometheus.Prometheus

import java.io.File
import scala.concurrent.ExecutionContext

/**
  * Contains the subcomponent of a bakery instance run on using the akka-runtime.
  * Subcomponents can be overridden to customize the bakery instance.
  *
  * @param optionalConfig A config instance used to load properties for the akka subcomponents.
  * @param externalContext Context passed to the default interactionManagerResource.
  */
class AkkaBakeryComponents(optionalConfig: Option[Config] = None,
                           externalContext: Option[Any] = None,
                           registry: CollectorRegistry = CollectorRegistry.defaultRegistry
                          ) extends LazyLogging {

  val metricService: MetricService = new MetricService(registry)

  def configResource: Resource[IO, Config] = Resource.eval(IO {
    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = optionalConfig.getOrElse(ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf"))))

    val production = config.getBoolean("baker.production-safe-mode")
    val loggingEnabled = config.getBoolean("baker.api-logging-enabled")

    if (production && loggingEnabled) {
      logger.error("Logging of API is enabled, but not allowed in production - stopping JVM")
      System.exit(1)
    }

    config
  })

  def externalContextOptionResource: Resource[IO, Option[Any]] =
    Resource.pure[IO, Option[Any]](externalContext)

  def actorSystemResource(config: Config): Resource[IO, ActorSystem] =
    Resource.make(
      acquire = IO(ActorSystem("baker", config)))(
      release = as => IO.fromFuture(IO(as.terminate()))(IO.contextShift(as.dispatcher)).map(_ => ())
    ).logResourceLifecycle("ActorSystem")

  def ec(actorSystem: ActorSystem): Resource[IO, ExecutionContext] = Resource.pure[IO, ExecutionContext](actorSystem.dispatcher)
  def cs(ec: ExecutionContext): Resource[IO, ContextShift[IO]] = Resource.pure[IO, ContextShift[IO]](IO.contextShift(ec))
  def timer(ec: ExecutionContext): Resource[IO, Timer[IO]] = Resource.pure[IO, Timer[IO]](IO.timer(ec))

  def akkaBakerTimeoutsResource(config: Config): Resource[IO, AkkaBakerConfig.Timeouts] =
    Resource.pure[IO, AkkaBakerConfig.Timeouts](AkkaBakerConfig.Timeouts(config)).logResourceLifecycle("Timeouts")

  def akkaBakerConfigValidationSettingsResource(config: Config): Resource[IO, AkkaBakerConfig.BakerValidationSettings] =
    Resource.pure[IO, AkkaBakerConfig.BakerValidationSettings](AkkaBakerConfig.BakerValidationSettings.from(config)).logResourceLifecycle("BakerValidationSettings")

  def bakerActorProviderResource(config: Config, timer: Timer[IO]): Resource[IO, BakerActorProvider] =
    Resource.pure[IO, BakerActorProvider](AkkaBakerConfig.bakerProviderFrom(config)).logResourceLifecycle("BakerActorProvider")

  def maybeCassandraResource(config: Config,
                             actorSystem: ActorSystem,
                             ec: ExecutionContext,
                             cs: ContextShift[IO],
                             timer: Timer[IO]): Resource[IO, Option[Cassandra]] =
    Cassandra.resource(config, actorSystem)(cs, timer, ec).logResourceLifecycle("Cassandra")

  def watcherResource(config: Config,
                      actorSystem: ActorSystem,
                      ec: ExecutionContext,
                      cs: ContextShift[IO],
                      timer: Timer[IO],
                      maybeCassandra: Option[Cassandra]): Resource[IO, Unit] =
    Watcher.resource(config, actorSystem, maybeCassandra)(cs, timer, ec).logResourceLifecycle("Watcher")

  def metricsOpsResource: Resource[IO, MetricsOps[IO]] =
    Prometheus.metricsOps[IO](metricService.registry, "http_interactions").logResourceLifecycle("Prometheus")

  def eventSinkResource(config: Config,
                        cs: ContextShift[IO],
                        timer: Timer[IO]): Resource[IO, EventSink] =
    EventSink.resource(config)(cs, timer).logResourceLifecycle("EventSink")

  def interactionManagerResource(config: Config,
                                 actorSystem: ActorSystem,
                                 externalContextOption: Option[Any]
                                ): Resource[IO, InteractionManager[IO]] =
    InteractionRegistry.resource(externalContextOption, metricService, config, actorSystem).logResourceLifecycle("InteractionManager")

  def recipeManagerResource(config: Config,
                            actorSystem: ActorSystem) : Resource[IO, RecipeManager] =
    Resource.pure[IO, RecipeManager](ActorBasedRecipeManager.getRecipeManagerActor(actorSystem, config)).logResourceLifecycle("RecipeManager")

  implicit class LoggingHelper[A](io: Resource[IO, A]) {
    def logResourceLifecycle(componentName: String): Resource[IO, A] = {
      val before = Resource.make(
        acquire = IO(logger.info(s"Creating $componentName")))(
        release = _ => IO(logger.info(s"$componentName resource released"))) // release goes backwards (FIFO)

      val after = Resource.make(
        acquire = IO(logger.info(s"Created $componentName")))(
        release = _ => IO(logger.info(s"Releasing $componentName resource")))

      for {
        _ <- before
        ioResult <- io
        _ <- after
      } yield ioResult
    }
  }

}
