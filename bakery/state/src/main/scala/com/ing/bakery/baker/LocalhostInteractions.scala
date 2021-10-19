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
import scala.jdk.CollectionConverters.collectionAsScalaIterableConverter

class LocalhostInteractions(config: Config,
                            system: ActorSystem,
                            val client: Client[IO],
                            port: Int = 0)
  extends DynamicInteractionManager with RemoteInteractionDiscovery with LazyLogging {
  private implicit val contextShift: ContextShift[IO] = IO.contextShift(system.dispatcher)
  private implicit val timer: Timer[IO] = IO.timer(system.dispatcher)
  private val apiUrlPrefix = config.getString("baker.interactions.localhost.api-url-prefix")
  private val localhostPort: Int =
    if (port == 0) config.getInt("baker.interactions.localhost.port")
    else port

  override def resource: Resource[IO, DynamicInteractionManager] = Resource.eval {
    for {
          interactions <- extractInteractions(client, Uri.unsafeFromString(s"http://localhost:$localhostPort$apiUrlPrefix"))
          _ = logger.info(s"localhost:$port: ${interactions.map(_.name).mkString(",")}")
          d <- discovered
        } yield {
      d.put(port.toString, interactions)
      this
    }
  }

}

