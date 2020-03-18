package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, Pod}
import com.ing.baker.baas.testing.BakeryFunSpec
import org.scalatest.{ConfigMap, Matchers}

import scala.sys.process._

class BakeryControllerSmokeTests extends BakeryFunSpec with Matchers {

  val webshopRecipeId = "9a2f8c2880ea8fc0"
  val reservationRecipeId = "79c890866238cf4b"

  describe("The Bakery Controller") {

    test("Creates, updates and deletes multiple independent recipes") { context =>
      val namespace = context.namespace
      for {
        webshop <- DefinitionFile("recipe-webshop.yaml", namespace)
        reservation <- DefinitionFile("recipe-reservation.yaml", namespace)

        _ <- eventually("All resources were created") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel("recipe" -> webshopRecipeId, namespace)
            reservationPodsCount <- Pod.countPodsWithLabel("recipe" -> reservationRecipeId, namespace)
            _ = webshopPodsCount shouldBe 2
            _ = reservationPodsCount shouldBe 2
            _ <- Pod.allPodsAreReady(namespace)
          } yield()
        }

        _ <- DefinitionFile("recipe-webshop-update.yaml", namespace)
        _ <- eventually("Webshop should upscale to 3 replicas") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel("recipe" -> webshopRecipeId, namespace)
            _ = webshopPodsCount shouldBe 3
          } yield ()
        }

        _ <- webshop.delete
        _ <- reservation.delete

        _ <- eventually("All resources were cleaned") {
          for {
            _ <- Pod.printPodsStatuses(namespace)
            webshopPodsCount <- Pod.countPodsWithLabel("recipe" -> webshopRecipeId, namespace)
            reservationPodsCount <- Pod.countPodsWithLabel("recipe" -> reservationRecipeId, namespace)
            _ = webshopPodsCount shouldBe 0
            _ = reservationPodsCount shouldBe 0
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
