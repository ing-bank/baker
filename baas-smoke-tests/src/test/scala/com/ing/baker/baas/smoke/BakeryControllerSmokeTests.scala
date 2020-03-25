package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, Pod}
import com.ing.baker.baas.testing.BakeryFunSpec
import org.scalatest.{ConfigMap, Matchers}

import scala.sys.process._

class BakeryControllerSmokeTests extends BakeryFunSpec with Matchers {

  val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
  val splitChar = if(isWindows) "\r\n" else "\n"

  val webshopBaker: (String, String) = "baker-name" -> "webshop-baker"
  val reservationBaker: (String, String) = "baker-name" -> "reservation-baker"
  val reserveItems: (String, String) = "interaction" -> "reserve-items"
  val shipItems: (String, String) = "interaction" -> "ship-items"
  val makePayment: (String, String) = "interaction" -> "make-payment"

  describe("The Bakery Controller") {

    test("Creates, updates and deletes multiple independent recipes") { context =>
      val namespace = context.namespace
      for {
        interactions <- DefinitionFile("interactions-example.yaml", namespace)
        _ <- eventually("All interactions were created") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            reserveItemsPodsCount <- Pod.countPodsWithLabel(reserveItems, namespace)
            shipItemsPodsCount <- Pod.countPodsWithLabel(shipItems, namespace)
            makePaymentPodsCount <- Pod.countPodsWithLabel(makePayment, namespace)
            _ = reserveItemsPodsCount shouldBe 2
            _ = shipItemsPodsCount shouldBe 1
            _ = makePaymentPodsCount shouldBe 1
            _ <- Pod.allPodsAreReady(namespace)
          } yield()
        }

        configOne <- Pod.execOnNamed("ship-items", namespace)("/bin/sh -c \"echo $ONE\"")
        configTwo <- Pod.execOnNamed("ship-items", namespace)("/bin/sh -c \"echo $TWO\"")
        configThree <- Pod.execOnNamed("ship-items", namespace)("/bin/sh -c \"echo $THREE\"")
        mountOne <- Pod.execOnNamed("ship-items", namespace)("ls /config")
        mountTwo <- Pod.execOnNamed("ship-items", namespace)("ls /secrets")

        _ = configOne shouldBe List(List("1"))
        _ = configTwo shouldBe List(List("one"))
        _ = configThree shouldBe List(List("admin"))
        _ = mountOne shouldBe List(List("ONE"))
        _ = mountTwo shouldBe List(List("username"))

        configOne <- Pod.execOnNamed("reserve-items", namespace)("/bin/sh -c \"echo $ONE\"")
        configTwo <- Pod.execOnNamed("reserve-items", namespace)("/bin/sh -c \"echo $TWO\"")
        configThree <- Pod.execOnNamed("reserve-items", namespace)("/bin/sh -c \"echo $THREE\"")
        mountOne <- Pod.execOnNamed("reserve-items", namespace)("ls /config").attempt.map {
          case Left(e) => e.getMessage
          case Right(a) => a.toString
        }
        mountTwo <- Pod.execOnNamed("reserve-items", namespace)("ls /secrets").attempt.map {
          case Left(e) => e.getMessage
          case Right(a) => a.toString
        }

        _ = configOne shouldBe List(List.empty, List.empty)
        _ = configTwo shouldBe List(List.empty, List.empty)
        _ = configThree shouldBe List(List.empty, List.empty)
        _ = mountOne shouldBe "Nonzero exit value: 2"
        _ = mountTwo shouldBe "Nonzero exit value: 2"
        _ <- printGreen("Interaction correctly configured")

        webshop <- DefinitionFile("baker-webshop.yaml", namespace)
        reservation <- DefinitionFile("baker-reservation.yaml", namespace)
        _ <- eventually("All recipes were created") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            _ <- Pod.allPodsAreReady(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel(webshopBaker, namespace)
            reservationPodsCount <- Pod.countPodsWithLabel(reservationBaker, namespace)
            _ = webshopPodsCount shouldBe 2
            _ = reservationPodsCount shouldBe 2
          } yield()
        }

        _ <- DefinitionFile("interactions-example-update.yaml", namespace)
        _ <- eventually("Interaction upscaled to 3 replicas") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            _ <- Pod.allPodsAreReady(namespace)
            reserveItemsPodsCount <- Pod.countPodsWithLabel(reserveItems, namespace)
            shipItemsPodsCount <- Pod.countPodsWithLabel(shipItems, namespace)
            makePaymentPodsCount <- Pod.countPodsWithLabel(makePayment, namespace)
            _ = reserveItemsPodsCount shouldBe 3
            _ = shipItemsPodsCount shouldBe 1
            _ = makePaymentPodsCount shouldBe 1
          } yield ()
        }

        _ <- DefinitionFile("baker-webshop-update-replicas.yaml", namespace)
        _ <- eventually("Webshop baker upscaled to 3 replicas") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            _ <- Pod.allPodsAreReady(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel(webshopBaker, namespace)
            _ = webshopPodsCount shouldBe 3
          } yield ()
        }

        _ <- DefinitionFile("baker-webshop-update-recipes.yaml", namespace)
        _ <- eventually("Webshop baker added an extra recipe") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            _ <- Pod.allPodsAreReady(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel(webshopBaker, namespace)
            _ = webshopPodsCount shouldBe 3

            podsRecipes <- Pod.execOnNamed("baas-state-webshop-baker", namespace)("ls /recipes").map(_.flatten)
            _ = assert(podsRecipes.contains("79c890866238cf4b"), "State pods should contain new recipe")
          } yield ()
        }

        _ <- interactions.delete
        _ <- webshop.delete
        _ <- reservation.delete

        _ <- eventually("All resources were cleaned") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel(webshopBaker, namespace)
            reservationPodsCount <- Pod.countPodsWithLabel(reservationBaker, namespace)
            reserveItemsPodsCount <- Pod.countPodsWithLabel(reserveItems, namespace)
            shipItemsPodsCount <- Pod.countPodsWithLabel(shipItems, namespace)
            makePaymentPodsCount <- Pod.countPodsWithLabel(makePayment, namespace)
            _ = webshopPodsCount shouldBe 0
            _ = reservationPodsCount shouldBe 0
            _ = reserveItemsPodsCount shouldBe 0
            _ = shipItemsPodsCount shouldBe 0
            _ = makePaymentPodsCount shouldBe 0
            services <- IO(s"kubectl get services -n $namespace".!!)
            deployments <- IO(s"kubectl get deployments -n $namespace".!!)
            replicasets <- IO(s"kubectl get replicasets -n $namespace".!!)
            _ = assert(services == "", "Services where still up while deleting namespace")
            _ = assert(deployments == "", "Deployments where still up while deleting namespace")
            _ = assert(replicasets == "", "Replica sets where still up while deleting namespace")
          } yield ()
        }
      } yield succeed
    }
  }

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext = smoke.BakeryControllerEnvironment.Context

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
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] =
    BakeryControllerEnvironment.resource(testArguments)

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
