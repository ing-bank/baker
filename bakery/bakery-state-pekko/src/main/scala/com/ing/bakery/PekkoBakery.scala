package com.ing.bakery

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.akka.{PekkoBaker, PekkoBakerConfig}
import com.ing.baker.runtime.akka.actor.LocalBakerActorProvider
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.bakery.components.PekkoBakeryComponents
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.CollectorRegistry
import org.apache.pekko.actor.ActorSystem
import org.apache.pekko.cluster.Cluster

import scala.concurrent.ExecutionContext

case class PekkoBakery(baker: PekkoBaker, system: ActorSystem) {
  def executionContext: ExecutionContext = system.dispatcher
}

object PekkoBakery extends LazyLogging {

  /**
    * Starts up an akka bakery instance by wiring up all the subcomponents with eachother, and starting an AkkaBakery instance
    *
    * @param abc A bakery component instance, containing the code to start up all bakery components
    * @return A resource which can be used to start up and gracefully shutdown a akka bakery instance.
    */
  def resource(abc: PekkoBakeryComponents): Resource[IO, PekkoBakery] = {
    for {
      config <- abc.configResource
      actorSystem <- abc.actorSystemResource(config)
      ec <- abc.ec(actorSystem)
      bakerActorProvider <- abc.bakerActorProviderResource(config)
      akkaBakerConfigTimeouts <- abc.akkaBakerTimeoutsResource(config)
      akkaBakerConfigValidationSettings <- abc.akkaBakerConfigValidationSettingsResource(config)
      maybeCassandra <- abc.maybeCassandraResource(config, actorSystem, ec)
      _ <- abc.watcherResource(config, actorSystem, ec, maybeCassandra)
      _ <- abc.metricsOpsResource
      eventSink <- abc.eventSinkResource(config)
      externalContext <- abc.externalContextOptionResource
      interactions <- abc.interactionManagerResource(config, actorSystem, externalContext)
      recipeManager <- abc.recipeManagerResource(config, actorSystem)
      baker <- Resource.make[IO, PekkoBaker](
        acquire = IO(PekkoBaker.apply(
          PekkoBakerConfig(
            interactions = interactions,
            recipeManager = recipeManager,
            bakerActorProvider = bakerActorProvider,
            timeouts = akkaBakerConfigTimeouts,
            bakerValidationSettings = akkaBakerConfigValidationSettings,
            terminateActorSystem = false, // terminating the actor system is done in it's own resource.
          )(actorSystem))))(
        release = baker => IO.fromFuture(IO(baker.gracefulShutdown()))
      )
      _ <- Resource.eval(eventSink.attach(baker))
      _ <- Resource.eval(IO.async_[Unit] { callback =>
        //If using local Baker the registerOnMemberUp is never called, should only be used during local testing.
        if (bakerActorProvider.isInstanceOf[LocalBakerActorProvider])
          callback(Right(()))
        else
          Cluster(actorSystem).registerOnMemberUp {
            logger.info("Akka cluster is now up")
            callback(Right(()))
          }})
    } yield PekkoBakery(baker, actorSystem)
  }
}

object Bakery {

  def akkaBakery(optionalConfig: Option[Config],
                 externalContext: Option[Any] = None,
                 interactionManager: Option[InteractionManager[IO]] = None,
                 recipeManager: Option[RecipeManager] = None,
                 metricService: MetricService = new MetricService(CollectorRegistry.defaultRegistry)): Resource[IO, PekkoBakery] = {

    val pekkoBakeryComponents: PekkoBakeryComponents =
      new PekkoBakeryComponents(optionalConfig, externalContext, metricService) {

        override def interactionManagerResource(config: Config,
                                                actorSystem: ActorSystem,
                                                externalContextOption: Option[Any]): Resource[IO, InteractionManager[IO]] =
          interactionManager match {
            case Some(value) => Resource.pure[IO, InteractionManager[IO]](value)
            case None => super.interactionManagerResource(config, actorSystem, externalContextOption)
          }


        override def recipeManagerResource(config: Config, actorSystem: ActorSystem): Resource[IO, RecipeManager] =
          recipeManager match {
            case Some(value) => Resource.pure[IO, RecipeManager](value)
            case None => super.recipeManagerResource(config, actorSystem)
          }
      }
    PekkoBakery.resource(pekkoBakeryComponents)
  }
}

