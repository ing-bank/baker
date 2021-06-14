package com.ing.bakery.baker

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._
import org.apache.kafka.clients.producer.{Callback, KafkaProducer, ProducerRecord, RecordMetadata}
import org.apache.kafka.common.serialization.StringSerializer

import scala.compat.java8.FutureConverters._
import java.util.Properties
import scala.concurrent.Promise
import scala.util.control.NonFatal
import scala.util.{Failure, Success, Try}



trait RecipeCache {
  def merge(recipes: List[RecipeRecord]): IO[List[RecipeRecord]] = IO(recipes)
  def close(): Unit = ()
}

object RecipeCache extends LazyLogging {

  private lazy val NoCache = IO { new RecipeCache { } }

  def resource(settings: Config)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, RecipeCache] = {

    Resource.make({
      val providerClass = settings.getString("provider-class")
      if (providerClass.isEmpty) {
        logger.info("No provider class specified: recipe cache disabled")
        NoCache
      } else {
        Try(Class.forName(providerClass).getDeclaredConstructor(classOf[com.typesafe.config.Config]).newInstance(settings)) match {
          case Success(cache: RecipeCache) =>
            logger.info(s"Using recipe cache implementation $providerClass")
            IO(cache)
          case Success(_) => {
            logger.warn(s"Recipe cache provider class $providerClass must extend ${RecipeCache.getClass.getCanonicalName}")
            NoCache
          }
          case Failure(exception) =>
            logger.error("Error initialising Kafka sink", exception)
            NoCache
        }
      }
    })(recipeCache => IO(recipeCache.close()))
  }
}

