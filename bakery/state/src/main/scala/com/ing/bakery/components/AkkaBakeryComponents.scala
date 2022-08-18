package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.actor.BakerActorProvider
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.{ActorBasedRecipeManager, RecipeManager}
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
                           externalContext: Option[Any] = None) extends LazyLogging {

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

  def externalContextOptionResource: Resource[IO, Option[Any]] = Resource.pure[IO, Option[Any]](externalContext)

  def actorSystemResource: Resource[IO, ActorSystem] = configResource.flatMap(config =>
    Resource.make(
      acquire = IO(ActorSystem("baker", config)))(
      release = as => IO.fromFuture(IO(as.terminate()))(IO.contextShift(as.dispatcher)).map(_ => ())
    )
  )
  val ec: Resource[IO, ExecutionContext] = actorSystemResource.map(_.dispatcher)
  val cs: Resource[IO, ContextShift[IO]] = ec.map(IO.contextShift)
  val timer: Resource[IO, Timer[IO]] = ec.map(IO.timer)

  def akkaBakerTimeoutsResource: Resource[IO, AkkaBakerConfig.Timeouts] =
    configResource.flatMap(config => Resource.eval(IO(AkkaBakerConfig.Timeouts(config))))

  def akkaBakerConfigValidationSettingsResource: Resource[IO, AkkaBakerConfig.BakerValidationSettings] =
    configResource.flatMap(config => Resource.eval(IO(AkkaBakerConfig.BakerValidationSettings.from(config))))

  def bakerActorProviderResource: Resource[IO, BakerActorProvider] =
    for {
      config <- configResource
    } yield AkkaBakerConfig.bakerProviderFrom(config)

  def maybeCassandraResource: Resource[IO, Option[Cassandra]] = for {
    config <- configResource
    actorSystem <- actorSystemResource
    ec <- ec
    cs <- cs
    timer <- timer
    result <- Cassandra.resource(config, actorSystem)(cs, timer, ec)
  } yield result

  def watcherResource: Resource[IO, Resource[IO, Unit]] = for {
    config <- configResource
    actorSystem <- actorSystemResource
    maybeCassandra <- maybeCassandraResource
    ec <- ec
    cs <- cs
    timer <- timer
  } yield Watcher.resource(config, actorSystem, maybeCassandra)(cs, timer, ec)

  def metricsOpsResource: Resource[IO, MetricsOps[IO]] =
    Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")

  def eventSinkResource: Resource[IO, EventSink] =
    for {
      config <- configResource
      cs <- cs
      timer <- timer
      eventSink <- EventSink.resource(config)(cs, timer)
    } yield eventSink

  def interactionManagerResource: Resource[IO, InteractionManager[IO]] =
    for {
      config <- configResource
      actorSystem <- actorSystemResource
      externalContextOption <- externalContextOptionResource
      interactionRegistry <- InteractionRegistry.resource(externalContextOption, config, actorSystem)
    } yield interactionRegistry

  def recipeManagerResource: Resource[IO, RecipeManager] = for {
    actorSystem <- actorSystemResource
    config <- configResource
  } yield ActorBasedRecipeManager.getRecipeManagerActor(actorSystem, config)


}
