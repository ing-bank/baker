package com.ing.baker.baas.dashboard

import java.net.InetSocketAddress

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.implicits._
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource}
import com.ing.baker.baas.dashboard.BakeryStateCache.{CacheRecipeInstanceMetadata, CacheRecipeMetadata}
import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.Encryption
import fs2.Stream
import fs2.concurrent.Queue
import io.circe.Json

import scala.concurrent.duration._

object Dashboard {

  // TODO temp while waiting for the http4s refactor
  case class EventListener private(eventStream: Stream[IO, BakerEvent], localAddress: InetSocketAddress)

  object EventListener {

    def resource(address: InetSocketAddress)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption, cs: ContextShift[IO]): Resource[IO, EventListener]  =
      for {
        queue <- Resource.liftF(Queue.unbounded[IO, BakerEvent])
        binding <- Resource.make {
          IO.fromFuture(IO(RemoteBakerEventListener.runWith(
            queue.enqueue1(_).unsafeRunSync(),
            address.getPort,
            10.seconds
          )))
        }(binding => IO.fromFuture(IO(binding.unbind())).void)
      } yield new EventListener(queue.dequeue, binding.localAddress)
  }


  def resource(stateServiceAddress: InetSocketAddress, eventListenerAddress: InetSocketAddress)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption, cs: ContextShift[IO]): Resource[IO, Dashboard] = {

    def buildCache(eventListener: EventListener): Stream[IO, Ref[IO, BakeryStateCache]] =
      for {
        cache <- Stream.eval(BakeryStateCache.emptyRef)
        updatingStream = eventListener.eventStream.evalMap(event => cache.update(_.handleEvent(event)))
        stateCache <- Stream.emit(cache).concurrently(updatingStream)
      } yield stateCache

    for {
      eventListener <- EventListener.resource(eventListenerAddress)
      cache <- buildCache(eventListener).compile.resource.lastOrError
      //stateClient <- IO(BakerClient(stateServiceHostname))
    } yield new Dashboard(/*stateClient,*/ cache, eventListener.localAddress)
  }
}

class Dashboard(/*stateClient: Baker,*/ cache: Ref[IO, BakeryStateCache], _eventListenerLocalAddress: InetSocketAddress)(implicit cs: ContextShift[IO]) {

  val eventListenerLocalAddress: InetSocketAddress = _eventListenerLocalAddress

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
