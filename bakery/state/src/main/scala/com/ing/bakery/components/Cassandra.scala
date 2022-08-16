package com.ing.bakery.components

import akka.actor.ActorSystem
import cats.effect.{Async, ContextShift, IO, Resource, Timer}
import com.datastax.oss.driver.api.core.CqlSession
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.{ExecutionContext, Future}

/**
  * This trait allows to implement custom Cassandra session providers, shared between multiple elements that need cassandra persistence.
  */
trait Cassandra {
  def session: Future[CqlSession]
}

object Cassandra extends LazyLogging {

  def resource(config: Config, system: ActorSystem)(implicit cs: ContextShift[IO], timer: Timer[IO], ec: ExecutionContext): Resource[IO, Option[Cassandra]] =
    Resource.eval[IO, Option[Cassandra]] {
      IO {
        val provider = config.getString("baker.cassandra.class")
        if (provider != "") {
          val configPath = config.getString("baker.cassandra.config-path")
          Some(Class
            .forName(provider)
            .getDeclaredConstructor(classOf[ActorSystem], classOf[Config], classOf[ExecutionContext])
            .newInstance(system, config.getConfig(configPath), ec)
            .asInstanceOf[Cassandra])
        } else None
      }
    }
}
