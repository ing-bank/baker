package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.datastax.oss.driver.api.core.CqlSession
import com.ing.baker.runtime.common.RecipeRecord
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging

import scala.util.{Failure, Success, Try}

trait RecipeCache {
  def init: IO[Unit] = IO.unit

  def merge(recipes: List[RecipeRecord]): IO[List[RecipeRecord]] = IO(recipes)

  def close(): Unit = ()
}

object RecipeCache extends LazyLogging {

  private lazy val NoCache = new RecipeCache {}

  def resource(config: Config, system: ActorSystem, maybeCassandra: Option[Cassandra])(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, RecipeCache] = {

    Resource.eval({
      maybeCassandra map { cassandra =>
        val clazz = config.getString("baker.recipe-cache.class")
        if (clazz.isEmpty) {
          logger.info("No class specified: recipe cache disabled")
          IO(NoCache)
        } else {
          for {
            session <- IO.fromFuture(IO(cassandra.session))
            cache <- IO(
              Try(Class.forName(clazz).getDeclaredConstructor(classOf[Config], classOf[CqlSession])
                .newInstance(config, session).asInstanceOf[RecipeCache]) match {
                case Success(cache: RecipeCache) =>
                  logger.info(s"Using recipe cache implementation $clazz")
                  cache
                case Success(_) =>
                  logger.warn(s"Recipe cache provider class $clazz must extend ${RecipeCache.getClass.getCanonicalName}")
                  NoCache
                case Failure(exception) =>
                  logger.error("Error initialising Kafka sink", exception)
                  NoCache
              })
            _ <- cache.init
          } yield cache
        }
      }
    } getOrElse IO(NoCache))
  }
}

