package com.ing.baker.baas.dashboard

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO}
import com.ing.baker.baas.dashboard.BakeryApi.{ BakeryStateCache, CacheRecipeMetadata, CacheRecipeInstanceMetadata }
import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import fs2.concurrent.Queue
import io.circe.Json
import io.circe.syntax._
import BakerEventEncoders._

import scala.concurrent.duration._

object BakeryApi {

  case class CacheRecipeMetadata(recipeId: String, recipeName: String, knownProcesses: Int, created: Long)

  case class CacheRecipeInstanceMetadata(recipeId: String, recipeInstanceId: String, created: Long)

  case class BakeryStateCache(inner: Map[String, (RecipeAdded, Map[String, (RecipeInstanceCreated, List[Json])])]) {

    def handleEvent(event: BakerEvent): BakeryStateCache = {
      println(Console.MAGENTA + event + Console.RESET)
      event match {
        case event: EventReceived =>
          recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
        case event: EventRejected =>
          copy()
        // TODO MISSING RECIPE ID FROM THIS EVENT!!!
        //recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
        case event: InteractionFailed =>
          recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
        case event: InteractionStarted =>
          recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
        case event: InteractionCompleted =>
          recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
        case event: RecipeInstanceCreated =>
          recipeInstanceCreated(event)
        case event: RecipeAdded =>
          recipeAdded(event)
      }
    }

    def recipeAdded(event: RecipeAdded): BakeryStateCache =
      copy(inner = inner + (event.recipeId -> (event, Map.empty)))

    def recipeInstanceCreated(event: RecipeInstanceCreated): BakeryStateCache = {
      val (recipeAddedEvent, instancesMap) = inner(event.recipeId)
      val newInstance = event.recipeInstanceId -> (event, List(recipeAddedEvent.asJson, event.asJson))
      copy(inner = inner + (event.recipeId -> (recipeAddedEvent -> (instancesMap + newInstance))))
    }

    def recipeInstanceEvent(recipeId: String, recipeInstanceId: String, event: Json): BakeryStateCache = {
      val (recipeAddedEvent, instancesMap) = inner(recipeId)
      val (instanceCreated, events) = instancesMap(recipeInstanceId)
      val newInstance = recipeInstanceId -> (instanceCreated, events.:+(event))
      copy(inner = inner + (recipeId -> (recipeAddedEvent -> (instancesMap + newInstance))))
    }

    def listRecipes: List[CacheRecipeMetadata] =
      inner.map { case (recipeId, (recipeAddedEvent, instances)) =>
        CacheRecipeMetadata(recipeId, recipeAddedEvent.recipeName, instances.size, recipeAddedEvent.date)
      }.toList

    def listInstances(recipeId: String): List[CacheRecipeInstanceMetadata] =
      inner.get(recipeId) match {
        case None =>
          List.empty
        case Some((_, instances)) =>
          instances.map { case (recipeInstanceId, (recipeInstanceCreatedEvent, _)) =>
            CacheRecipeInstanceMetadata(recipeId, recipeInstanceId, recipeInstanceCreatedEvent.timeStamp)
          }.toList
      }

    def listEvents(recipeId: String, recipeInstanceId: String): List[Json] =
      inner
        .get(recipeId)
        .flatMap(_._2.get(recipeInstanceId))
        .map(_._2)
        .getOrElse(List.empty)

    def getRecipe(recipeId: String): Option[RecipeAdded] =
      inner
        .get(recipeId)
        .map(_._1)

    def getRecipeInstance(recipeId: String, recipeInstanceId: String): Option[(RecipeAdded, RecipeInstanceCreated)] =
      inner
        .get(recipeId)
        .flatMap { case (recipeAdded, instances) =>
            instances.get(recipeInstanceId).map(recipeAdded -> _._1)
        }
  }

  object BakeryStateCache {

    def empty =
      BakeryStateCache(Map.empty)

    def emptyRef: IO[Ref[IO, BakeryStateCache]] =
      Ref.of[IO, BakeryStateCache](BakeryStateCache.empty)
  }

  def runWith(stateServiceHostname: String, listenerPort: Int)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): IO[BakeryApi] = {
    implicit val cs: ContextShift[IO] = IO.contextShift(system.dispatcher)
    for {
      cache <- BakeryStateCache.emptyRef
      bakerEventListener <- Queue.unbounded[IO, BakerEvent]
      _ <-
        IO(RemoteBakerEventListener.runWith(
          bakerEventListener.enqueue1(_).unsafeRunSync(),
          listenerPort,
          10.seconds
        ))
      _ <- IO(bakerEventListener
        .dequeue
        .evalMap { event => cache.update(_.handleEvent(event)) }
        .compile
        .drain
        .unsafeRunAsyncAndForget()
      )
      //stateClient <- IO(BakerClient(stateServiceHostname))
    } yield new BakeryApi(/*stateClient,*/ cache)
  }
}

class BakeryApi(/*stateClient: Baker,*/ cache: Ref[IO, BakeryStateCache])(implicit cs: ContextShift[IO]) {

  def listRecipes: IO[List[CacheRecipeMetadata]] =
    cache.get.map(_.listRecipes)

  def listInstances(recipeId: String): IO[List[CacheRecipeInstanceMetadata]] =
    cache.get.map(_.listInstances(recipeId))

  def listEvents(recipeId: String, recipeInstanceId: String): IO[List[Json]] =
    cache.get.map(_.listEvents(recipeId, recipeInstanceId))

  def getRecipe(recipeId: String): IO[Option[RecipeAdded]] =
    cache.get.map(_.getRecipe(recipeId))

  def getRecipeInstance(recipeId: String, recipeInstanceId: String): IO[Option[(RecipeAdded, RecipeInstanceCreated)]] =
    cache.get.map(_.getRecipeInstance(recipeId, recipeInstanceId))

  def logEvents(): Unit = {
    cache
      .get
      .map(state => println(state))
      .unsafeRunSync()
  }
}
