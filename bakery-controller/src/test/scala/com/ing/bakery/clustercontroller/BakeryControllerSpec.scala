package com.ing.bakery.clustercontroller

import java.util.UUID

import cats.implicits._
import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.ops.{BakerOperations, BakerResource, InteractionOperations, InteractionResource}
import com.ing.bakery.mocks.{KubeApiServer, WatchEvent}
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.mockserver.integration.ClientAndServer
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import skuber.api.client.KubernetesClient

import scala.concurrent.duration._

class BakeryControllerSpec extends BakeryFunSpec with Matchers {

  describe("Bakery Controller") {

    test("Creates a baker") { context =>
      for {
        _ <- context.kubeApiServer.resourceWatchResponds(WatchEvent.BakersPath, WatchEvent.Added, WatchEvent.recipeResource)
        _ <- IO.sleep(10.seconds)
      } yield succeed
    }
  }

  case class Context(kubeApiServer: KubeApiServer)

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

    def getResourceDirectoryPathSafe: String = {
      val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
      val safePath = getClass.getResource("/recipes").getPath
      if (isWindows) safePath.tail
      else safePath
    }

    for {
      // Mock server
      mockServer <- Resource.make(IO(ClientAndServer.startClientAndServer(0)))(s => IO(s.stop()))
      kubeApiServer = new KubeApiServer(mockServer)

      makeActorSystem = IO {
        ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
          """
            |akka {
            |  #stdout-loglevel = "OFF"
            |  #loglevel = "OFF"
            |}
            |""".stripMargin)) }
      stopActorSystem = (system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated) }).void
      system <- Resource.make(makeActorSystem)(stopActorSystem)
      materializer = ActorMaterializer()(system)
      k8s: KubernetesClient = skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServer.getLocalPort))(system, materializer)
      _ <- Resource.liftF(kubeApiServer.resourceWatchRespondsEmpty(WatchEvent.BakersPath))
      _ <- Resource.liftF(kubeApiServer.resourceWatchRespondsEmpty(WatchEvent.InteractionsPath))

      _ <- ResourceOperations.controller(k8s, InteractionOperations.spec)(contextShift, timer, system, materializer, InteractionResource.interactionResourceFormat, InteractionResource.resourceDefinitionInteractionResource)
      _ <- ResourceOperations.controller(k8s, BakerOperations.spec)(contextShift, timer, system, materializer, BakerResource.recipeResourceFormat, BakerResource.resourceDefinitionRecipeResource)
    } yield Context(kubeApiServer)
  }

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
