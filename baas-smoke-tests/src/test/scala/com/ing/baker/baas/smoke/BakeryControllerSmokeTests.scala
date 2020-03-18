package com.ing.baker.baas.smoke

import cats.effect.{IO, Resource}
import com.ing.baker.baas.smoke
import com.ing.baker.baas.smoke.k8s.{DefinitionFile, Pod}
import com.ing.baker.baas.testing.BakeryFunSpec
import org.scalatest.{ConfigMap, Matchers}
import scala.sys.process._

class BakeryControllerSmokeTests extends BakeryFunSpec with Matchers {

  describe("The Bakery Controller") {

    test("Creates, updates and deletes multiple independent recipes") { context =>
      for {
        webshop <- DefinitionFile("recipe-webshop.yaml", context.namespace)
        reservation <- DefinitionFile("recipe-reservation.yaml", context.namespace)

        _ <- eventually(Pod.allPodsAreReady(context.namespace))
        webshopPodsCount <- Pod.countPodsWithLabel("recipe" -> "lol", context.namespace)
        reservationPodsCount <- Pod.countPodsWithLabel("recipe" -> "lol", context.namespace)
        _ <- printGreen("All resources were created")

        _ <- webshop.delete
        _ <- reservation.delete
        _ <- eventually(for {
          pods <- IO(s"kubectl get pods -n ${context.namespace}".!!)
          services <- IO(s"kubectl get services -n ${context.namespace}".!!)
          deployments <- IO(s"kubectl get deployments -n ${context.namespace}".!!)
          replicasets <- IO(s"kubectl get replicasets -n ${context.namespace}".!!)
          _ = assert(!pods.contains("Running"), "There were still running pods while deleting namespace")
          _ = assert(services == "", "Services where still up while deleting namespace")
          _ = assert(deployments == "", "Deployments where still up while deleting namespace")
          _ = assert(replicasets == "", "replica sets where still up while deleting namespace")
        } yield ())
        _ <- printGreen("All resources were cleaned")
      } yield 1 shouldBe 1
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
    ???

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
