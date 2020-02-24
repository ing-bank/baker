package com.ing.baker.baas.recipelistener

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import com.ing.baker.baas.testing.BakeryFunSpec
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.types.PrimitiveValue
import org.http4s.{Status, Uri}
import org.scalatest.ConfigMap

import scala.concurrent.Promise
import scala.util.Success

class RemoteEventListenerSpec extends BakeryFunSpec {

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

  describe("The remote recipe event listener") {

    test("execute apply") { context =>
      val eventReceived: Promise[(RecipeEventMetadata, EventInstance)] = Promise()
      val listenerFunction: (RecipeEventMetadata, EventInstance) => Unit =
        (metadata, event) => eventReceived.complete(Success(metadata -> event))
      val receivedEvents = IO.fromFuture(IO(eventReceived.future))
      for {
        _ <- context.withEventListener(listenerFunction)
        status <- context.clientFiresEvent(recipeEventMetadata, event)
        result <- receivedEvents
      } yield {
        assert(status.code == 200)
        assert(recipeEventMetadata == result._1 && event == result._2)
      }
    }
  }

  case class Context(
    withEventListener: ((RecipeEventMetadata, EventInstance) => Unit) => IO[Unit],
    clientFiresEvent: (RecipeEventMetadata, EventInstance) => IO[Status]
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
    val eventListenerPromise: Promise[(RecipeEventMetadata, EventInstance) => Unit] =
      Promise()
    val localEventListener: (RecipeEventMetadata, EventInstance) => Unit =
      (m, e) => eventListenerPromise.future.foreach(_.apply(m, e))
    for {
      server <- RemoteEventListenerService.resource(localEventListener, InetSocketAddress.createUnresolved("localhost", 0))
      client <- RemoteEventListenerClient.resource(server.baseUri, executionContext)
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
