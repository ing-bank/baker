package com.ing.bakery

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.{ActorBasedRecipeManager, RecipeManager}
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.bakery.components.{Cassandra, EventSink, InteractionRegistry, Watcher}
import com.typesafe.config.{Config, ConfigFactory}
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import org.http4s.metrics.prometheus.Prometheus

import java.io.File
import scala.concurrent.ExecutionContext

case class AkkaBakery(baker: Baker, system: ActorSystem) {
  def executionContext: ExecutionContext = system.dispatcher
}

object Bakery extends LazyLogging {

  def akkaBakery(optionalConfig: Option[Config],
                 externalContext: Option[Any] = None,
                 interactionManager: Option[InteractionManager[IO]] = None,
                 recipeManager: Option[RecipeManager] = None) : Resource[IO, AkkaBakery] = {
    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = optionalConfig.getOrElse(ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf"))))
    val bakerConfig = config.getConfig("baker")

    val production = bakerConfig.getBoolean("production-safe-mode")
    val loggingEnabled = bakerConfig.getBoolean("api-logging-enabled")

    if (production && loggingEnabled) {
      logger.error("Logging of API is enabled, but not allowed in production - stopping JVM")
      System.exit(1)
    }

    implicit val system: ActorSystem = ActorSystem("baker", config)
    implicit val executionContext: ExecutionContext = system.dispatcher
    implicit val cs: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Timer[IO] = IO.timer(executionContext)
    for {
      maybeCassandra <- Cassandra.resource(config, system)
      _ <- Watcher.resource(config, system, maybeCassandra)
      _ <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "http_interactions")
      eventSink <- EventSink.resource(config)
      interactions <- InteractionRegistry.resource(externalContext, config, system)
      baker = AkkaBaker.apply(
        AkkaBakerConfig(
        externalContext = externalContext,
        interactions = interactionManager.getOrElse(interactions),
        recipeManager =  recipeManager.getOrElse(ActorBasedRecipeManager.getRecipeManagerActor(system, config)),
        bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
        timeouts = AkkaBakerConfig.Timeouts.apply(config),
        bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config))(system))
      _ <- Resource.make(IO {baker})(baker => IO.fromFuture(IO(baker.gracefulShutdown())))
      _ <- Resource.eval(eventSink.attach(baker))
      _ <- Resource.eval(IO.async[Unit] { callback =>
        //If using local Baker the registerOnMemberUp is never called, should onl be used during local testing.
        if (config.getString("baker.actor.provider") == "local")
          callback(Right(()))
        else
          Cluster(system).registerOnMemberUp {
            logger.info("Akka cluster is now up")
            callback(Right(()))
          }
      })

    } yield AkkaBakery(baker, system)
  }
}

