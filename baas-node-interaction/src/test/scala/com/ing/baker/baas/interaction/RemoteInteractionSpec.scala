package com.ing.baker.baas.interaction

import java.net.InetSocketAddress

import cats.effect.{IO, Resource}
import com.ing.baker.baas.testing.BakeryFunSpec
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}
import com.ing.baker.types.{CharArray, Int64, PrimitiveValue, Type}
import org.scalatest.ConfigMap
import org.scalatest.compatible.Assertion

import scala.concurrent.Future

class RemoteInteractionSpec extends BakeryFunSpec {

  case class Context(
    withInteractionInstance: InteractionInstance => (RemoteInteractionClient => IO[Assertion]) => IO[Assertion]
  )

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
    val context = Context({ interaction => runTest =>
      RemoteInteractionService.resource(interaction, InetSocketAddress.createUnresolved("localhost", 0))
        .flatMap(server => RemoteInteractionClient.resource(server.baseUri, executionContext))
        .use(runTest)
    })
    Resource.pure[IO, Context](context)
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

    val implementation = InteractionInstance(
      name = "TestInteraction",
      input = Seq(CharArray, Int64),
      run = input => Future.successful(Some(result(input.head.value.as[String], input(1).value.as[Int])))
    )

    test("publishes its interface") { context =>
      context.withInteractionInstance(implementation) { client =>
        for {
          result <- client.interface
          (name: String, input: Seq[Type]) = result
        } yield assert(name == implementation.name && input === implementation.input)
      }
    }

    test("executes the interaction") { context =>
      context.withInteractionInstance(implementation) { client =>
        val ingredient0 = IngredientInstance("input0", PrimitiveValue("A"))
        val ingredient1 = IngredientInstance("input1", PrimitiveValue(1))
        for {
          result0 <- client.runInteraction(Seq(ingredient0, ingredient1))
        } yield assert(result0 === Some(result("A", 1)))
      }
    }
  }
}
