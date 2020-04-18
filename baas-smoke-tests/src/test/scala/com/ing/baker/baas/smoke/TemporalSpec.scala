package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, Pod}
import com.ing.baker.baas.testing.BakeryFunSpec
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import scala.concurrent.duration._

class TemporalSpec extends BakeryFunSpec with Matchers {

  val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
  val splitChar = if(isWindows) "\r\n" else "\n"

  val webshopBaker: (String, String) = "baker-name" -> "webshop-baker"
  val reservationBaker: (String, String) = "baker-name" -> "reservation-baker"
  val reserveItems: (String, String) = "interaction" -> "reserve-items"
  val makePaymentAndShipItems: (String, String) = "interaction" -> "make-payment-and-ship-items"

  describe("The Temporal Test Setup") {

    test("ordering of setup") { context =>
      val namespace = context.namespace

      BlazeClientBuilder[IO](executionContext).resource.use { client =>
        for {
          _ <- context.inspector.watchLogs("bakery-controller", None, namespace)
          _ <- DefinitionFile("baker-webshop.yaml", namespace)
          _ <- eventually("All recipes were created") {
            for {
              _ <- Pod.printPodsStatuses(namespace)
              _ <- Pod.allPodsAreReady(namespace)
              _ <- context.inspector.watchLogsWithPrefix("baas-state", None, namespace)
              webshopPodsCount <- Pod.countPodsWithLabel(webshopBaker, namespace)
              _ = webshopPodsCount shouldBe 2
            } yield ()
          }

          _ <- printGreen(s"\nCreating client app")
          _ <- DefinitionFile("example-client-app.yaml", namespace)
          _ <- Pod.waitUntilAllPodsAreReady(namespace)
          _ <- context.inspector.watchLogsWithPrefix("client-app", Some("client-app"), namespace)

          managementClient = new StateNodeManagementClient(client, Uri.unsafeFromString("http://localhost:8080"))

          _ <- DefinitionFile("interactions-example.yaml", namespace)
          _ <- eventually("All interactions were created") {
            for {
              _ <- Pod.printPodsStatuses(namespace)
              reserveItemsPodsCount <- Pod.countPodsWithLabel(reserveItems, namespace)
              makePaymentPodsCount <- Pod.countPodsWithLabel(makePaymentAndShipItems, namespace)
              _ <- context.inspector.watchLogsWithPrefix("reserve-items", None, namespace)
              _ <- context.inspector.watchLogsWithPrefix("make-payment-and-ship-items", None, namespace)
              _ = reserveItemsPodsCount shouldBe 2
              _ = makePaymentPodsCount shouldBe 1
              _ <- Pod.allPodsAreReady(namespace)
            } yield ()
          }

          _ <- eventually("State node discovered the interactions") {
            for {
              interactions <- managementClient.knownInteractionNames
              _ = println(Console.MAGENTA + interactions + Console.RESET)
              _ = interactions.length shouldBe 3
              _ = interactions should contain("ReserveItems")
              _ = interactions should contain("MakePayment")
              _ = interactions should contain("ShipItems")
            } yield ()
          }
        } yield succeed
      }
    }
  }

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = smoke.BakeryControllerEnvironment.Context

  /** Represents external arguments to the test context builder. */
  type TestArguments = smoke.BakeryControllerEnvironment.Arguments

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, smoke.BakeryControllerEnvironment.Context] =
    BakeryControllerEnvironment.resource(testArguments)

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = {
    config.getOrElse("debug", "false") match {
      case "yes" | "true" | "t" | "y" => smoke.BakeryControllerEnvironment.Arguments(debugMode = true)
      case _ => smoke.BakeryControllerEnvironment.Arguments(debugMode = false)
    }
  }
}
