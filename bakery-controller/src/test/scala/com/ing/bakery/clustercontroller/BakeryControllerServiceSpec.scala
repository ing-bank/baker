package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import com.ing.bakery.testing.BakeryFunSpec
import org.http4s.Method._
import org.http4s.client.dsl.io._
import org.http4s.Uri
import org.http4s.client.Client
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers

class BakeryControllerServiceSpec extends BakeryFunSpec with Matchers {

  case class Context(client: Client[IO], port: Int)

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
    val address: InetSocketAddress = InetSocketAddress.createUnresolved("localhost", 0)
    for {
      server <- BakeryControllerService.resource(address)
      client <- BlazeClientBuilder[IO](executionContext).resource
    } yield Context(client, server.address.getPort)
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()

  test("Health endpoint") { context =>
    context.client.status(GET(Uri.unsafeFromString(s"http://localhost:${context.port}") / "api" / "bakery" / "health")).map(status => assert(status.code == 200))
  }
}
