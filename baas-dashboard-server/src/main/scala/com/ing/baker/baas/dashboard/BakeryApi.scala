package com.ing.baker.baas.dashboard

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO}
import com.ing.baker.baas.dashboard.BakeryApi.BakeryStateCache
import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import fs2.concurrent.Queue
import io.circe.Json
import io.circe.generic.auto._
import io.circe.syntax._

import scala.concurrent.duration._

object BakeryApi {

  case class RecipeMetadata(recipeId: String, recipeName: String, knownProcesses: Int, created: Long)

  case class RecipeInstanceMetadata(recipeId: String, recipeInstanceId: String, created: Long)

  case class BakeryStateCache(inner: Map[String, (RecipeAdded, Map[String, (RecipeInstanceCreated, List[Json])])]) extends AnyVal {

    def handleEvent(event: BakerEvent): BakeryStateCache = event match {
      case event: EventReceived =>
        recipeInstanceEvent(event.recipeId, event.recipeInstanceId, event.asJson)
      case event: EventRejected =>
        copy()
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

    def recipeAdded(event: RecipeAdded): BakeryStateCache =
      copy(inner = inner + (event.recipeId -> (event, Map.empty)))

    def recipeInstanceCreated(event: RecipeInstanceCreated): BakeryStateCache = {
      val newInstance = event.recipeInstanceId -> (event, List.empty)
      val (recipeAddedEvent, instancesMap) = inner(event.recipeId)
      copy(inner = inner + (event.recipeId -> (recipeAddedEvent -> (instancesMap + newInstance))))
    }

    def recipeInstanceEvent(recipeId: String, recipeInstanceId: String, event: Json): BakeryStateCache = {
      val (recipeAddedEvent, instancesMap) = inner(recipeId)
      val (instanceCreated, events) = instancesMap(recipeInstanceId)
      val newInstance = recipeInstanceId -> (instanceCreated, events.:+(event))
      copy(inner = inner + (recipeId -> (recipeAddedEvent -> (instancesMap + newInstance))))
    }

    def listRecipes: List[RecipeMetadata] =
      inner.map { case (recipeId, (recipeAddedEvent, instances)) =>
        RecipeMetadata(recipeId, recipeAddedEvent.recipeName, instances.size, recipeAddedEvent.date)
      }.toList

    def listInstances(recipeId: String): List[RecipeInstanceMetadata] =
      inner.get(recipeId) match {
        case None =>
          List.empty
        case Some((_, instances)) =>
          instances.map { case (recipeInstanceId, (recipeInstanceCreatedEvent, _)) =>
            RecipeInstanceMetadata(recipeId, recipeInstanceId, recipeInstanceCreatedEvent.timeStamp)
          }.toList
      }

    def getEvents(recipeId: String, recipeInstanceId: String): List[Json] =
      inner
        .get(recipeId)
        .flatMap(_._2.get(recipeInstanceId))
        .map(_._2)
        .getOrElse(List.empty)
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
      _ <- bakerEventListener
        .dequeue
        .evalMap(event => cache.update(_.handleEvent(event)))
        .compile
        .drain
      //stateClient <- IO(BakerClient(stateServiceHostname))
    } yield new BakeryApi(/*stateClient,*/ cache)
  }
}

class BakeryApi(/*stateClient: Baker,*/ cache: Ref[IO, BakeryStateCache])(implicit cs: ContextShift[IO]) {

  val ec = scala.concurrent.ExecutionContext.Implicits.global

  def logEvents: Unit = {
    def print(color: String) = cache.get.map(state => println(color + state + Console.RESET))
    print(Console.BLUE).flatMap(_ => IO.sleep(1.second)(IO.timer(ec))).unsafeRunAsyncAndForget()
    print(Console.RED).unsafeRunAsyncAndForget()
  }

  //def getAllRecipes: Future[]
}
