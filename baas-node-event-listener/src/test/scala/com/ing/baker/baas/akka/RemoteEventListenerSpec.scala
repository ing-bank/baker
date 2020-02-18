package com.ing.baker.baas.akka

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.implicits._
import com.ing.baker.baas.akka.RemoteEventListenerSpec._
import com.ing.baker.baas.scaladsl.RemoteEventListener
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.PrimitiveValue
import com.typesafe.config.ConfigFactory
import org.scalatest.AsyncFlatSpec
import org.scalatest.compatible.Assertion

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.Try

class RemoteEventListenerSpec extends AsyncFlatSpec {

  "The Remote Event Listener" should "execute on apply" in {
    val eventReceived: Promise[(RecipeEventMetadata, EventInstance)] = Promise()
    val listenerFunction: (RecipeEventMetadata, EventInstance) => Unit =
      (metadata, event) => eventReceived.complete(Try(metadata -> event))
    testWith (listenerFunction, { client =>
      for {
        _ <- client(recipeEventMetadata, event)
        result <- eventReceived.future
      } yield assert(recipeEventMetadata == result._1 && event == result._2)
    })
  }
}

object RemoteEventListenerSpec {

  val recipeEventMetadata: RecipeEventMetadata =
    RecipeEventMetadata(
      recipeId = "recipe-id",
      recipeName = "Recipe",
      recipeInstanceId = "instance-id"
    )

  val event: EventInstance =
    EventInstance(
      name = "Result",
      providedIngredients = Map(
        "data" -> PrimitiveValue("hello-world")
      )
    )

  def testWith[F[_], Lang <: LanguageApi]
  (listenerFunction: (RecipeEventMetadata, EventInstance) => Unit, test: (RemoteEventListenerClient) => Future[Assertion])
  (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName, ConfigFactory.parseString("""akka.loglevel = "OFF" """))
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (binding, port) <- withOpenPort(5000, port => RemoteEventListener.runWith(listenerFunction, port, 20.seconds))
      client = RemoteEventListenerClient(s"http://localhost:$port/")
      assertion <- test(client)
      _ <- binding.unbind()
    } yield assertion
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T])(implicit ec: ExecutionContext): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> (_, port)).recoverWith {
          case _: java.net.BindException => search(tail)
          //case _: ChannelException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
