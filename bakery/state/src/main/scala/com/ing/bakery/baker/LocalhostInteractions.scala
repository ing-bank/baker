package com.ing.bakery.baker

import akka.actor.ActorSystem
import akka.stream.scaladsl.{Keep, RestartSource, Sink, Source}
import akka.stream._
import akka.{Done, NotUsed}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits.catsSyntaxApplicativeError
import com.ing.baker.runtime.akka.internal.DiscoveringInteractionManager
import com.ing.baker.runtime.model.InteractionInstance
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import skuber.api.client.{EventType, KubernetesClient}
import skuber.json.format._
import skuber.{K8SWatchEvent, LabelSelector, ListOptions, Service}

import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`
import scala.concurrent.Future
import scala.concurrent.duration.DurationInt
import cats.syntax.traverse._

class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: Client[IO])
  extends DiscoveringInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  private implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  private implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
  private val apiUrlPrefix = config.getString("baker.interactions.api-url-prefix")
  private val localhostPorts = config.getIntList("baker.interactions.localhost-ports")

  override def resource: Resource[IO, DiscoveringInteractionManager] = Resource.eval {
    IO {
      localhostPorts.map(port =>
        extractInteractions(client, Uri.unsafeFromString(s"http://localhost:$port$apiUrlPrefix"))
          .flatMap(interactions => discovered
            .flatMap(d => IO(d.put(port.toString, interactions))))).toList.traverse(_ => IO.unit)
      this
    }
  }

}

