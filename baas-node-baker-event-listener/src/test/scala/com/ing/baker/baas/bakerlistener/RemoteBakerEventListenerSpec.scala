package com.ing.baker.baas.bakerlistener

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import com.ing.baker.baas.testing.BakeryFunSpec
import com.ing.baker.runtime.scaladsl.{BakerEvent, RecipeInstanceCreated}
import org.http4s.Status
import org.scalatest.ConfigMap

import scala.concurrent.Promise
import scala.util.Success

class RemoteBakerEventListenerSpec extends BakeryFunSpec {

  val event: BakerEvent =
    RecipeInstanceCreated(
      timeStamp = 42,
      recipeId = "recipe-id",
      recipeName = "recipe-name",
      recipeInstanceId = "recipe-instance-id"
    )

  describe("The remote baker recipe event listener") {

    test("execute apply") { context =>
      val eventReceived: Promise[BakerEvent] = Promise()
      val listenerFunction: BakerEvent => Unit =
        event => eventReceived.complete(Success(event))
      val receivedEvents = IO.fromFuture(IO(eventReceived.future))
      for {
        _ <- context.withEventListener(listenerFunction)
        status <- context.clientFiresEvent(event)
        result <- receivedEvents
      } yield {
        assert(status.code == 200)
        assert(event == result)
      }
    }
  }

  case class Context(
    withEventListener: (BakerEvent => Unit) => IO[Unit],
    clientFiresEvent: BakerEvent => IO[Status]
  )

  /** Represents the "sealed resources context" that each test can use. */
  override type TestContext = Context
  /** Represents external arguments to the test context builder. */
  override type TestArguments = Unit

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
   * For example web servers, network connection, database mocks.
   *
   * The objective of this function is to provide "sealed resources context" to each test, that means context
   * that other tests simply cannot touch.
   *
   * @param testArguments arguments built by the `argumentsBuilder` function.
   * @return the resources each test can use
   */
  override def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] = {
    val eventListenerPromise: Promise[BakerEvent => Unit] =
      Promise()
    val localEventListener: BakerEvent => Unit =
      event => eventListenerPromise.future.foreach(_.apply(event))
    for {
      server <- RemoteBakerEventListenerService.resource(localEventListener, InetSocketAddress.createUnresolved("localhost", 0))
      client <- RemoteBakerEventListenerClient.resource(server.baseUri, executionContext)
    } yield Context(
      withEventListener = listener => IO(eventListenerPromise.complete(Success(listener))),
      clientFiresEvent = client.apply
    )
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
   *
   * @param config map populated with the -Dkey=value arguments.
   * @return the data structure used by the `contextBuilder` function.
   */
  override def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
