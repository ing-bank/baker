package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client

/**
  * Discovers interactions running on localhost
  */
class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: Client[IO],
                            port: Option[Int] = None)
  extends DynamicInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  protected implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  protected implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
  protected def apiUrlPrefix: String = config.getString("baker.interactions.localhost.api-url-prefix")
  protected def localhostPort: Int = port.getOrElse(config.getInt("baker.interactions.localhost.port"))

  override def resource: Resource[IO, DynamicInteractionManager] = Resource.eval {
    for {
          interactions <- extractInteractions(client, Uri.unsafeFromString(s"http://localhost:$localhostPort$apiUrlPrefix"))
          d <- discovered
        } yield {
      d.put(port.toString, interactions)
      this
    }
  }

}

