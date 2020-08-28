package com.ing.bakery.client

import java.net.InetSocketAddress

import cats.effect.concurrent.MVar
import cats.effect.{IO, Resource}
import com.ing.bakery.common.{KeystoreConfig, TLSConfig}
import com.ing.bakery.javadsl
import com.ing.bakery.scaladsl.BakerClient
import com.ing.baker.runtime.common.RecipeInstanceMetadata
import com.ing.baker.runtime.scaladsl.BakerResult
import com.ing.baker.runtime.serialization.JsonEncoders._
import io.circe.generic.auto._
import org.http4s.{Header, _}
import org.http4s.circe._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.server.blaze._
import org.scalatest.ConfigMap

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.ExecutionContext

class BakerClientSpec extends BakeryFunSpec {

  case class Context(serverAddress: InetSocketAddress, receivedHeaders: IO[List[Header]])

  val serviceTLSConfig: TLSConfig =
    TLSConfig(
      KeystoreConfig("changeit", "test-certs/server.jks", "JKS"),
      KeystoreConfig("changeit", "test-certs/server.jks", "JKS")
    )

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

    def testServer(receivedHeaders: MVar[IO, List[Header]]): HttpApp[IO] = {
      implicit val bakerResultEntityEncoder: EntityEncoder[IO, BakerResult] = jsonEncoderOf[IO, BakerResult]
      Router("/api/bakery/instances" ->  HttpRoutes.of[IO] {
        case request@GET -> Root =>
          for {
            _ <- receivedHeaders.put(request.headers.toList)
            response <- Ok(BakerResult(List.empty[Int]))
          } yield response
      }).orNotFound
    }

    val sslConfig = serviceTLSConfig.loadSSLContext
    val sslParams = sslConfig.getDefaultSSLParameters
    sslParams.setNeedClientAuth(true)
    for {
      receivedHeaders <- Resource.liftF(MVar.empty[IO, List[Header]])
      service <- BlazeServerBuilder[IO](ExecutionContext.global)
        .withSslContextAndParameters(sslConfig, sslParams)
        .bindSocketAddress(InetSocketAddress.createUnresolved("localhost", 0))
        .withHttpApp(testServer(receivedHeaders))
        .resource
    } yield Context(service.address, receivedHeaders.take)
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
   *
   * @param config map populated with the -Dkey=value arguments.
   * @return the data structure used by the `contextBuilder` function.
   */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()

  describe("The baker client") {

    test("scaladsl - connects with mutual tls and adds headers to requests") { context =>
      val uri = Uri.unsafeFromString(s"https://localhost:${context.serverAddress.getPort}/")
      val testHeader = Header("X-Test", "Foo")
      val filter: Request[IO] => Request[IO] = _.putHeaders(testHeader)
      BakerClient.resource(uri, executionContext, List(filter), Some(clientTLSConfig)).use { client =>
        for {
          _ <- IO.fromFuture(IO(client.getAllRecipeInstancesMetadata))
          headers <- context.receivedHeaders
        } yield assert(headers.contains(testHeader))
      }
    }

    test("javadsl - connects with mutual tls and adds headers to requests") { context =>
      val uri = s"https://localhost:${context.serverAddress.getPort}/"
      val testHeader = Header("X-Test", "Foo")
      val filter: java.util.function.Function[Request[IO], Request[IO]] = _.putHeaders(testHeader)
      for {
        client <- IO.fromFuture(IO(FutureConverters.toScala(javadsl.BakerClient.build(uri, List(filter).asJava, java.util.Optional.of(clientTLSConfig)))))
        _ <- IO.fromFuture(IO(FutureConverters.toScala(client.getAllRecipeInstancesMetadata)))
        headers <- context.receivedHeaders
      } yield assert(headers.contains(testHeader))
    }
  }
}
