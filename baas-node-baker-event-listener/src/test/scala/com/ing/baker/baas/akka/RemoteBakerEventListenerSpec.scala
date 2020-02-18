package com.ing.baker.baas.akka

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.implicits._
import com.ing.baker.baas.akka.RemoteBakerEventListenerSpec._
import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{BakerEvent, RecipeInstanceCreated}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory
import org.scalatest.AsyncFlatSpec
import org.scalatest.compatible.Assertion

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.Try

class RemoteBakerEventListenerSpec extends AsyncFlatSpec {

  "The Remote Event Listener" should "execute on apply" in {
    val eventReceived: Promise[BakerEvent] = Promise()
    val listenerFunction: BakerEvent => Unit =
      event => eventReceived.complete(Try(event))
    testWith (listenerFunction, { client =>
      for {
        _ <- client(event)
        result <- eventReceived.future
      } yield assert(event == result)
    })
  }
}

object RemoteBakerEventListenerSpec {

  val event: BakerEvent =
    RecipeInstanceCreated(
      timeStamp = 42,
      recipeId = "recipe-id",
      recipeName = "recipe-name",
      recipeInstanceId = "recipe-instance-id"
    )

  def testWith[F[_], Lang <: LanguageApi]
  (listenerFunction: BakerEvent => Unit, test: RemoteBakerEventListenerClient => Future[Assertion])
  (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName, ConfigFactory.parseString("""akka.loglevel = "OFF" """))
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (binding, port) <- withOpenPort(5000, port => RemoteBakerEventListener.runWith(listenerFunction, port, 20.seconds))
      client = RemoteBakerEventListenerClient(s"http://localhost:$port/")
      assertion <- test(client)
      _ <- binding.unbind()
    } yield assertion
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T])(implicit ec: ExecutionContext): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> (_, port)).recoverWith {
          case _: java.net.BindException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
