package com.ing.baker.baas.dashboard

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.{ContextShift, IO}
import cats.effect.concurrent.Ref
import com.ing.baker.baas.scaladsl.{BakerClient, RemoteBakerEventListener}
import com.ing.baker.baas.dashboard.BakeryApi.{BakeryStateCache, Machinery}
import com.ing.baker.runtime.scaladsl.{Baker, BakerEvent, RecipeInformation}
import com.ing.baker.runtime.serialization.Encryption
import fs2.concurrent.Queue
import fs2.Stream

import scala.concurrent.duration._

object BakeryApi {

  type BakeryStateCache = Map[String, (RecipeInformation, List[String])]

  case class Machinery(cache: Ref[IO, BakeryStateCache], bakerEventListener: Stream[IO, BakerEvent])

  def runWith(stateServiceHostname: String, listenerPort: Int)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): IO[BakeryApi] = {
    implicit val cs: ContextShift[IO] = IO.contextShift(system.dispatcher)
    for {
      cache <- Ref.of[IO, BakeryStateCache](Map.empty)
      bakerEventListener <- Queue.unbounded[IO, BakerEvent]
      _ <-
        IO(RemoteBakerEventListener.runWith(
          { event =>
            println(event)
            bakerEventListener.enqueue1(event).unsafeRunAsyncAndForget()
          },
          listenerPort,
          10.seconds
        ))
      //stateClient <- IO(BakerClient(stateServiceHostname))
    } yield new BakeryApi(/*stateClient,*/ Machinery(cache, bakerEventListener.dequeue))
  }
}

class BakeryApi(/*stateClient: Baker,*/ machinery: Machinery)(implicit cs: ContextShift[IO]) {

  def logEvents: IO[Unit] = {
    def print(color: String) = machinery
      .bakerEventListener
      .evalMap(event => IO(println(color + event + Console.RESET)))
    print(Console.RED).compile.drain
  }

  //def getAllRecipes: Future[]
}
