package com.ing.baker.baas.akka

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.implicits._
import com.ing.baker.baas.akka.RemoteInteractionSpec._
import com.ing.baker.baas.scaladsl.RemoteInteraction
import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.runtime.serialization.Encryption
import com.ing.baker.types.{CharArray, Int64, PrimitiveValue}
import org.jboss.netty.channel.ChannelException
import org.scalatest.AsyncFlatSpec
import org.scalatest.compatible.Assertion

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future}

class RemoteInteractionSpec extends AsyncFlatSpec {

  "The Remote Interaction" should "execute on apply" in {
    testWith (implementation, { client =>
      val ingredient0 = IngredientInstance("input0", PrimitiveValue("A"))
      val ingredient1 = IngredientInstance("input1", PrimitiveValue(1))
      for {
        result0 <- client(Seq(ingredient0, ingredient1))
      } yield assert(result0 === Some(result("A", 1)))
    })
  }
}

object RemoteInteractionSpec {

  def result(input0: String, input1: Int) = EventInstance(
    name = "Result",
    providedIngredients = Map(
      "data" -> PrimitiveValue(input0 + input1)
    )
  )

  val implementation = InteractionInstance(
    name = "TestInteraction",
    input = Seq(CharArray, Int64),
    run = input => Future.successful(Some(result(input.head.value.as[String], input(1).value.as[Int])))
  )

  def testWith[F[_], Lang <: LanguageApi]
  (implementation: InteractionInstance, test: (RemoteInteractionClient) => Future[Assertion])
  (implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption
    for {
      (binding, port) <- withOpenPort(5000, port => RemoteInteraction.runWith(implementation, port, 20.seconds))
      client = RemoteInteractionClient(s"http://localhost:$port/")
      assertion <- test(client)
      _ <- binding.unbind()
    } yield assertion
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T])(implicit ec: ExecutionContext): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> (_, port)).recoverWith {
          case _: java.net.BindException => search(tail)
          case _: ChannelException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
