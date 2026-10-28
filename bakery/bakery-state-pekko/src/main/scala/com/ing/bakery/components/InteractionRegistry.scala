package com.ing.bakery.components

import cats.Traverse
import cats.effect.{IO, Resource}
import cats.syntax.all._
import com.ing.baker.runtime.core.util.DynamicInteractionManager
import com.ing.baker.runtime.defaultinteractions
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceInput}
import com.ing.baker.types.Type
import com.ing.bakery.interaction.{BaseRemoteInteractionClient, RemoteInteractionClient}
import com.ing.bakery.metrics.MetricService
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.apache.pekko.actor.ActorSystem
import org.http4s.blaze.client.BlazeClientBuilder
import org.http4s.client.Client
import org.http4s.{Headers, Uri}
import scalax.collection.ChainingOps

import java.io.IOException
import scala.concurrent.duration.{DurationInt, FiniteDuration}

object InteractionRegistry extends LazyLogging {

  def resource(externalContext: Option[Any], metricService: MetricService, config: Config, actorSystem: ActorSystem): Resource[IO, InteractionRegistry] = {
    readInteractionClassName(config)
      .map(Class.forName)
      .getOrElse(classOf[BaseInteractionRegistry])
      .tap(c => logger.info(s"Interaction registry: ${c.getName}"))
      .getDeclaredConstructor(classOf[Config], classOf[MetricService], classOf[ActorSystem])
      .newInstance(config, metricService, actorSystem)
      .asInstanceOf[InteractionRegistry]
      .resource(externalContext)
  }

  private def readInteractionClassName(config: Config): Option[String] = {
    Some(config.getString("baker.interactions.class")).filterNot(_.isEmpty)
  }
}


/**
  * Registry of interactions, bundles together several interaction managers that provide actual interactions.
  * It also implements InteractionManager[IO] interface, thus for Baker it won't matter if it talks to
  * a single interaction manager or to a registry.
  */
trait InteractionRegistry extends InteractionManager[IO] {
  def resource(externalContext: Option[Any]): Resource[IO, InteractionRegistry]

  def interactionManagers: IO[List[InteractionManager[IO]]]
}

/**
  * Bundles together interactions of all available interaction managers
  */
trait TraversingInteractionRegistry extends InteractionRegistry {
  override def listAll: IO[List[InteractionInstance[IO]]] =
    interactionManagers
      .flatMap(_.traverse(_.listAll).map(_.flatten))
      .flatMap(managed => IO.pure(defaultinteractions.all ++ managed))
}

/**
  * Base implementation of interaction registry
  */
class BaseInteractionRegistry(config: Config, metricService: MetricService, actorSystem: ActorSystem)
  extends TraversingInteractionRegistry
    with LazyLogging {

  // variable state, but changed only once when the resource is started
  protected var managers: List[InteractionManager[IO]] = List.empty[InteractionManager[IO]]

  override def interactionManagers: IO[List[InteractionManager[IO]]] = IO.pure(managers)

  override def resource(externalContext: Option[Any]): Resource[IO, InteractionRegistry] = {
    for {
      client <- BlazeClientBuilder[IO](actorSystem.dispatcher).resource
      interactionManagers <- interactionManagersResource(client, metricService)
    } yield {
      managers = interactionManagers
      logger.info(s"Initialised interaction registry with managers: ${managers.map(_.getClass.getName).mkString(",")}")
      this
    }
  }

  protected def interactionManagersResource(client: Client[IO], metricService: MetricService): Resource[IO, List[InteractionManager[IO]]] = {

    val interactionClient = new BaseRemoteInteractionClient(client, Headers.empty, metricService)

    def getRemoteInteractions: Option[DynamicInteractionManager] = {
      val path = "baker.interactions.remote.class"

      def noneIfEmpty(str: String): Option[String] = if (str.isEmpty) None else Some(str)

      if (config.hasPath(path)) noneIfEmpty(config.getString(path)).map {
        Class.forName(_)
          .getDeclaredConstructor(classOf[Config], classOf[ActorSystem], classOf[RemoteInteractionClient])
          .newInstance(config, actorSystem, interactionClient)
          .asInstanceOf[DynamicInteractionManager]
      } else {
        None
      }
    }

    val local = new LocalhostInteractions(config, interactionClient)

    val lists = getRemoteInteractions
      .map(r => List(local, r))
      .getOrElse(List(local))
      .map(_.resource)

    Traverse[List].sequence(lists)
  }
}
