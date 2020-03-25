package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import cats.implicits._
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

        webshop <- DefinitionFile("baker-webshop.yaml", namespace)
        reservation <- DefinitionFile("baker-reservation.yaml", namespace)
        kafkaEventSink <- DefinitionFile("kafka-event-sink.yaml", namespace)

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

            pods <- IO(s"kubectl get --no-headers=true pods -o name -n ${context.namespace}".!!).map(_.split(splitChar).toList)
            regex = """pod\/(baas-state-webshop-baker.+)""".r
            webshopPods = pods.mapFilter {
              case regex(podName) => Some(podName)
              case _ => None
            }
            podsRecipes <- webshopPods
              .traverse { pod =>
                IO(s"kubectl exec $pod -n ${context.namespace} -- ls /recipes".!!)
                  .map(_.split(splitChar).toList)
              }.map(_.flatten)

            _ = assert(podsRecipes.contains("79c890866238cf4b"), "State pods should contain new recipe")

          } yield ()
        }

        _ <- interactions.delete
        _ <- webshop.delete
        _ <- reservation.delete
        _ <- kafkaEventSink.delete

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
