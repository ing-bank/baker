package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri
import org.http4s.client.Client
import cats.effect.Temporal

/**
  * Discovers interactions running on localhost
  */
class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: Client[IO],
                            port: Option[Int] = None)
  extends DynamicInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  protected implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  protected implicit val timer: Temporal[IO] = IO.timer(system.dispatcher)
  protected def apiUrlPrefix: String = config.getString("baker.interactions.localhost.api-url-prefix")
  protected def localhostPort: Int = port.getOrElse(config.getInt("baker.interactions.localhost.port"))

  override def resource: Resource[IO, DynamicInteractionManager] = Resource.eval {
    val url = s"http://localhost:$localhostPort$apiUrlPrefix"
    for {
      remoteInteractions <- extractInteractions(client, Uri.unsafeFromString(url))
      d <- discovered
        } yield {
      logger.info(s"${url} provides ${remoteInteractions.interactions.size} interactions: ${remoteInteractions.interactions.map(_.name).mkString(",")}")
      d.put(port.toString, InteractionBundle(remoteInteractions.startedAt, remoteInteractions.interactions))
      this
    }
  }

}

