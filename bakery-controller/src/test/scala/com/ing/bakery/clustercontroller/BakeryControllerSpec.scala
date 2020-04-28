package com.ing.bakery.clustercontroller

import java.util.UUID

import cats.implicits._
import akka.actor.ActorSystem
import akka.stream.ActorMaterializer
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.types.CharArray
import com.ing.bakery.clustercontroller.BakeryControllerSpec._
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, InteractionController, InteractionResource}
import com.ing.bakery.mocks.{KubeApiServer, RemoteInteraction}
import com.ing.bakery.mocks.WatchEvent.ResourcePath
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.http4s.client.blaze.BlazeClientBuilder
import org.mockserver.integration.ClientAndServer
import org.scalatest.ConfigMap
import org.scalatest.matchers.should.Matchers
import skuber.api.client.KubernetesClient
import skuber.{EnvVar, ObjectMeta}

import scala.concurrent.Future
import scala.concurrent.duration._

object BakeryControllerSpec {

  val interactionResource: InteractionResource = InteractionResource(
    metadata = ObjectMeta(name = "localhost"),
    spec = InteractionResource.Spec(
      image = "interaction.image:1.0.0",
      replicas = 2,
      env = List(
        EnvVar("ONE", EnvVar.StringValue("one")),
        EnvVar("TWO", EnvVar.ConfigMapKeyRef(name = "my-config-map", key = "two")),
        EnvVar("THREE", EnvVar.SecretKeyRef(name = "my-secret", key = "three"))
      ),
      configMapMounts = List(InteractionResource.ConfigMount(name = "my-config-map", mountPath = "/my-config")),
      secretMounts = List(InteractionResource.ConfigMount(name = "my-secret", mountPath = "/my-secrets"))
    )
  )

  val interaction: InteractionInstance = InteractionInstance(
    name = "interaction-one",
    input = Seq(CharArray),
    run = _ => Future.successful(None)
  )

  val bakerResource: BakerResource = BakerResource(
    metadata = ObjectMeta(name = "RecipeOne"),
    spec = BakerResource.Spec(
      bakeryVersion = "3.0.2-SNAPSHOT",
      replicas = 2,
      recipes = List("CgdXZWJzaG9wErEQChYKFAoQdW5hdmFpbGFibGVJdGVtcxABCkVaQwo/ChdTaGlwcGluZ0FkZHJlc3NSZWNlaXZlZBIkCg9zaGlwcGluZ0FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREAEKEwoRCg1yZXNlcnZlZEl0ZW1zEAEKCwoJCgVpdGVtcxABCg8KDQoJU2hpcEl0ZW1zEAIKnANimQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhAaDgjoBxEAAAAAAAAAQBgFCkhaRgpCChpQYXltZW50SW5mb3JtYXRpb25SZWNlaXZlZBIkChJwYXltZW50SW5mb3JtYXRpb24SDiIMCgoKBGluZm8SAggREAEKFVoTCg8KDVBheW1lbnRGYWlsZWQQAApQWk4KSgoLT3JkZXJQbGFjZWQSHAoHb3JkZXJJZBIRIg8KDQoHb3JkZXJJZBICCBESHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAEKFQoTCg9zaGlwcGluZ0FkZHJlc3MQAQpKWkgKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAAK2wNi2AMKcQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggRCg8KDVBheW1lbnRGYWlsZWQScQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREg8KDVBheW1lbnRGYWlsZWQiFgoQcmVjaXBlSW5zdGFuY2VJZBICCBEiPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWIiQKD3NoaXBwaW5nQWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEiJAoScGF5bWVudEluZm9ybWF0aW9uEg4iDAoKCgRpbmZvEgIIESoLTWFrZVBheW1lbnQyC01ha2VQYXltZW50UhAaDgjoBxEAAAAAAAAAQBgFClVaUwpPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFhAAChMKEQoNc2hpcHBpbmdPcmRlchABChlaFwoTChFTaGlwcGluZ0NvbmZpcm1lZBAACndadQpxChFQYXltZW50U3VjY2Vzc2Z1bBJcCg1zaGlwcGluZ09yZGVyEksiSQodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYKHAoHYWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEQAAoRCg8KC01ha2VQYXltZW50EAIKGAoWChJwYXltZW50SW5mb3JtYXRpb24QAQoSChAKDFJlc2VydmVJdGVtcxACCrMBYrABChMKEVNoaXBwaW5nQ29uZmlybWVkEhMKEVNoaXBwaW5nQ29uZmlybWVkIlwKDXNoaXBwaW5nT3JkZXISSyJJCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFgocCgdhZGRyZXNzEhEiDwoNCgdhZGRyZXNzEgIIESoJU2hpcEl0ZW1zMglTaGlwSXRlbXNSEBoOCOgHEQAAAAAAAABAGAUKDQoLCgdvcmRlcklkEAESBggLEBAYARIGCBEQCxgBEiAIEhAKGAEiGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIVCBIQDBgBIg1JdGVtc1Jlc2VydmVkEgYIAhALGAESBggGEBEYARIGCAgQFBgBEgYICBADGAESBggBEAkYARIGCAkQCxgBEgYIBRASGAESBggDEAUYARIGCAwQAhgBEgYIChAAGAESBggNEBMYARIZCAQQDhgBIhFTaGlwcGluZ0NvbmZpcm1lZBIGCA8QDRgBEhkIEBAPGAEiEVBheW1lbnRTdWNjZXNzZnVsEhUIEBAHGAEiDVBheW1lbnRGYWlsZWQSBggTEAQYARIGCBQQBRgBOhA5YTJmOGMyODgwZWE4ZmMw")
    )
  )
}

class BakeryControllerSpec extends BakeryFunSpec with Matchers {

  describe("Bakery Controller") {

    test("Creates interactions") { context =>
      context.interactionController.use( _ =>
        for {
          _ <- context.kubeApiServer.expectCreationOf("expectations/interaction-deployment.json", ResourcePath.DeploymentsPath)
          _ <- context.kubeApiServer.expectCreationOf("expectations/interaction-service.json", ResourcePath.ServicesPath, context.adaptHttpPortToMockServerPort)
          _ <- context.kubeApiServer.expectCreationOf("expectations/interaction-creation-config-map.json", ResourcePath.ConfigMapsPath, context.adaptHttpPortToMockServerPort)
          _ <- context.kubeApiServer.createInteractions(interactionResource)
          _ <- context.remoteInteraction.publishesItsInterface(interaction)
          _ <- eventually(for {
            _ <- context.kubeApiServer.validateCreationOf(ResourcePath.DeploymentsPath)
            _ <- context.kubeApiServer.validateCreationOf(ResourcePath.ServicesPath)
            _ <- context.remoteInteraction.interfaceWasQueried(interaction)
            _ <- context.kubeApiServer.validateCreationOf(ResourcePath.ConfigMapsPath)
          } yield succeed)
        } yield succeed
      )
    }
  }

  case class Context(
    kubeApiServer: KubeApiServer,
    remoteInteraction: RemoteInteraction,
    adaptHttpPortToMockServerPort: String => String,
    bakerController: Resource[IO, Unit],
    interactionController: Resource[IO, Unit]
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
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] =
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

      httpClient <- BlazeClientBuilder[IO](executionContext).resource
      interactionController =
        Resource.liftF(kubeApiServer.noNewInteractionEvents).flatMap( _ =>
          new InteractionController(httpClient).watch(k8s)(contextShift, timer, system, materializer, InteractionResource.interactionResourceFormat, InteractionResource.resourceDefinitionInteractionResource))
      bakerController =
        Resource.liftF(kubeApiServer.noNewBakerEvents).flatMap( _ =>
          new BakerController().watch(k8s)(contextShift, timer, system, materializer, BakerResource.recipeResourceFormat, BakerResource.resourceDefinitionRecipeResource))
    } yield Context(
      kubeApiServer,
      new RemoteInteraction(mockServer),
      _.replace("{{http-api-port}}", mockServer.getLocalPort.toString),
      bakerController,
      interactionController
    )

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments = ()
}
