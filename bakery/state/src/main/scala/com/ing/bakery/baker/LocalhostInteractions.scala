package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.syntax.traverse._
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client

import scala.collection.convert.ImplicitConversions.`collection AsScalaIterable`

class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: Client[IO])
  extends DynamicInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  private implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  private implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
  private val apiUrlPrefix = config.getString("baker.interactions.api-url-prefix")
  private val localhostPorts = config.getIntList("baker.interactions.localhost-ports")

  override def resource: Resource[IO, DynamicInteractionManager] = Resource.eval {
    IO {
      localhostPorts.map(port =>
        extractInteractions(client, Uri.unsafeFromString(s"http://localhost:$port$apiUrlPrefix"))
          .flatMap(interactions => discovered
            .flatMap(d => IO(d.put(port.toString, interactions))))).toList.traverse(_ => IO.unit)
      this
    }
  }

}

