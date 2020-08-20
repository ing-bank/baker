package com.ing.bakery.client

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import com.ing.baker.baas.common.TLSConfig
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.types.{CharArray, Int64, PrimitiveValue}
import org.http4s.Header
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.blaze._

import scala.concurrent.{ExecutionContext, Future}

class BakerClientSpec extends BakeryFunSpec {

  case class Context(receivedHeaders: IO[List[Header]])

  val serviceTLSConfig: TLSConfig =
    TLSConfig("changeit", "test-certs/server.jks", "JKS")

  val clientTLSConfig: TLSConfig =
    TLSConfig("changeit", "test-certs/client.jks", "JKS")

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = Unit



  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
   * For example web servers, network connection, database mocks.
   *
   * The objective of this function is to provide "sealed resources context" to each test, that means context
   * that other tests simply cannot touch.
   *
   * @param testArguments arguments built by the `argumentsBuilder` function.
   * @return the resources each test can use
   */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] = {
    val sslConfig = BakerClient.loadSSLContext(serviceTLSConfig)
    val sslParams = sslConfig.getDefaultSSLParameters
    sslParams.setNeedClientAuth(true)
    BlazeServerBuilder[IO](executionContext)
      .withSslContextAndParameters(sslConfig, sslParams)
      .bindSocketAddress(InetSocketAddress.createUnresolved("localhost", 0))
      .withHttpApp(new HealthService().build)
      .resource
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
   *
   * @param config map populated with the -Dkey=value arguments.
   * @return the data structure used by the `contextBuilder` function.
   */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()

  describe("The remote interaction") {

    def result(input0: String, input1: Int) = EventInstance(
      name = "Result",
      providedIngredients = Map(
        "data" -> PrimitiveValue(input0 + input1)
      )
    )

    val implementation0 = InteractionInstance(
      name = "TestInteraction0",
      input = Seq(CharArray, Int64).toList,
      run = input => Future.successful(Some(result(input.head.value.as[String], input(1).value.as[Int])))
    )

    val implementation1 = InteractionInstance(
      name = "TestInteraction1",
      input = Seq(CharArray, Int64),
      run = input => Future.successful(Some(result(input.head.value.as[String] + "!", input(1).value.as[Int] + 1)))
    )

    test("publishes its interface") { context =>
      context.withInteractionInstances(List(implementation0, implementation1)) { client =>
        for {
          result <- client.interface
        } yield assert(result == List(
          I.Interaction(implementation0.shaBase64, implementation0.name, implementation0.input.toList),
          I.Interaction(implementation1.shaBase64, implementation1.name, implementation1.input.toList)
        ))
      }
    }

    test("executes the interaction") { context =>
      context.withInteractionInstances(List(implementation0, implementation1)) { client =>
        val ingredient0 = IngredientInstance("input0", PrimitiveValue("A"))
        val ingredient1 = IngredientInstance("input1", PrimitiveValue(1))
        for {
          result0 <- client.runInteraction(implementation0.shaBase64, Seq(ingredient0, ingredient1))
          result1 <- client.runInteraction(implementation1.shaBase64, Seq(ingredient0, ingredient1))
        } yield {
          assert(result0 === Some(result("A", 1)))
          assert(result1 === Some(result("A!", 2)))
        }
      }
    }

    test("does not make connections with clients that does not trust") { context =>
      context.withNoTrustClient(List(implementation0)) { client =>
        val ingredient0 = IngredientInstance("input0", PrimitiveValue("A"))
        val ingredient1 = IngredientInstance("input1", PrimitiveValue(1))
        val result: IO[Option[String]] = client.runInteraction(implementation0.shaBase64, Seq(ingredient0, ingredient1))
          .map(_ => None)
          .handleErrorWith {
            case e: java.net.ConnectException => IO.pure(Some("connection error"))
            case e => IO.raiseError(e)
          }
        result.map(result => assert(result === Some("connection error")))
      }
    }
  }
}
