package com.ing.bakery

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.akka.actor.LocalBakerActorProvider
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.recipe_manager.RecipeManager
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.bakery.components.AkkaBakeryComponents
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.ExecutionContext

case class AkkaBakery(baker: Baker, system: ActorSystem) {
  def executionContext: ExecutionContext = system.dispatcher
}

object AkkaBakery extends LazyLogging {

  /**
    * Starts up an akka bakery instance by wiring up all the subcomponents with eachother, and starting an AkkaBakery instance
    *
    * @param abc A bakery component instance, containing the code to start up all bakery components
    * @return A resource which can be used to start up and gracefully shutdown a akka bakery instance.
    */
  def resource(abc: AkkaBakeryComponents): Resource[IO, AkkaBakery] = {
    for {
      config <- abc.configResource
      actorSystem <- abc.actorSystemResource(config)
      ec <- abc.ec(actorSystem)
      cs <- abc.cs(ec)
      timer <- abc.timer(ec)
      akkaBakerConfigTimeouts <- abc.akkaBakerTimeoutsResource(config)
      akkaBakerConfigValidationSettings <- abc.akkaBakerConfigValidationSettingsResource(config)
      maybeCassandra <- abc.maybeCassandraResource(config, actorSystem, ec, cs, timer)
      _ <- abc.watcherResource(config, actorSystem, ec, cs, timer, maybeCassandra)
      _ <- abc.metricsOpsResource
      eventSink <- abc.eventSinkResource(config, cs, timer)
      externalContext <- abc.externalContextOptionResource
      interactions <- abc.interactionManagerResource(config, actorSystem, externalContext)
      recipeManager <- abc.recipeManagerResource(config, actorSystem)
      bakerActorProvider <- abc.bakerActorProviderResource(config)
      baker = AkkaBaker.apply(
        AkkaBakerConfig(
          externalContext = externalContext,
          interactions = interactions,
          recipeManager = recipeManager,
          bakerActorProvider = bakerActorProvider,
          timeouts = akkaBakerConfigTimeouts,
          bakerValidationSettings = akkaBakerConfigValidationSettings
        )(actorSystem))
      _ <- Resource.make(IO(baker))(baker => IO.fromFuture(IO(baker.gracefulShutdown()))(cs))
      _ <- Resource.eval(eventSink.attach(baker)(cs))
      _ <- Resource.eval(IO.async[Unit] { callback =>
        //If using local Baker the registerOnMemberUp is never called, should only be used during local testing.
        if (bakerActorProvider.isInstanceOf[LocalBakerActorProvider])
          callback(Right(()))
        else
          Cluster(actorSystem).registerOnMemberUp {
            logger.info("Akka cluster is now up")
            callback(Right(()))
          }
      })

    } yield AkkaBakery(baker, actorSystem)
  }
}

object Bakery {

  def akkaBakery(optionalConfig: Option[Config],
                 externalContext: Option[Any] = None,
                 interactionManager: Option[InteractionManager[IO]] = None,
                 recipeManager: Option[RecipeManager] = None) : Resource[IO, AkkaBakery] = {
    val akkaBakeryComponents = new AkkaBakeryComponents(optionalConfig, externalContext) {

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
    AkkaBakery.resource(akkaBakeryComponents)
  }
}

