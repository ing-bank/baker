package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.akka.internal.DynamicInteractionManager
import com.ing.bakery.interaction.RemoteInteractionClient
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import org.http4s.Uri

/**
  * Discovers interactions running on localhost
  */
class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: RemoteInteractionClient)
  extends DynamicInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  protected def apiUrlPrefix: String = config.getString("baker.interactions.localhost.api-url-prefix")
  protected def localhostPort: Int = config.getInt("baker.interactions.localhost.port")

  override def resource: Resource[IO, DynamicInteractionManager] = Resource.eval {
    val url = s"http://localhost:$localhostPort$apiUrlPrefix"
    for {
      remoteInteractions <- extractInteractions(client, Uri.unsafeFromString(url))
      d <- discovered
        } yield {
      logger.info(s"${url} provides ${remoteInteractions.interactions.size} interactions: ${remoteInteractions.interactions.map(_.name).mkString(",")}")
      d.put(url, InteractionBundle(remoteInteractions.startedAt, remoteInteractions.interactions))
      this
    }
  }
}

