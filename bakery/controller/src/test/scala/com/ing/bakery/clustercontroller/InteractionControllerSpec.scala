package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.{ForceRollingUpdateOnConfigMapUpdate, InteractionController, InteractionResource}
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.mocks.RemoteInteraction
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.mockserver.integration.ClientAndServer
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.{ConfigMap, Pod, PodList, Service}

class InteractionControllerSpec extends BakeryFunSpec with KubernetesMockito {

  test("creates a interaction (CRD)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: InteractionResource = BakeryControllerFixtures.interactionResource.copy()
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    for {
      _ <- mockCreate(Deployment(interaction.name))
      _ <- mockCreate(Service(interaction.name).copy(spec =
        Some(Service.Spec(ports = mockedServicePort))))
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerFixtures.interaction)
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- mockCreate(ConfigMap(interaction.name + "-manifest"))
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.ADDED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyCreate[Deployment](_.name == interaction.name)
          _ <- verifyCreate[Service](_.name == interaction.name)
          _ <- verifyCreate[ConfigMap](_.name == interaction.name + "-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
          _ <- context.remoteInteraction.interfaceWasQueried
        } yield ()
      }
    } yield succeed
  }

  test("updates a interaction (CRD)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: InteractionResource = BakeryControllerFixtures.interactionResource.copy()
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    for {
      _ <- mockUpdate(Deployment(interaction.name))
      _ <- mockCreate(Service(interaction.name).copy(spec =
        Some(Service.Spec(ports = mockedServicePort))))
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerFixtures.interaction)
      _ <- mockUpdate[ConfigMap](ConfigMap(interaction.name + "-manifest"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.MODIFIED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.remoteInteraction.interfaceWasQueried
          _ <- verifyUpdate[Deployment](_.name == interaction.name)
          _ <- verifyUpdate[ConfigMap](_.name == interaction.name + "-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
        } yield ()
      }
    } yield succeed
  }

  test("updates a interaction (CRD) Backwards compatibility of interactions with no publishing version") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: InteractionResource = BakeryControllerFixtures.interactionResource.copy()
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    for {
      _ <- mockUpdate(Deployment(interaction.name))
      _ <- mockCreate(Service(interaction.name).copy(spec =
        Some(Service.Spec(ports = mockedServicePort))))
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerFixtures.interaction)
      _ <- mockUpdate[ConfigMap](ConfigMap(interaction.name + "-manifest"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.MODIFIED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.remoteInteraction.interfaceWasQueried
          _ <- verifyUpdate[Deployment](_.name == interaction.name)
          _ <- verifyUpdate[ConfigMap](_.name == interaction.name + "-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
        } yield ()
      }
    } yield succeed
  }

  test("delete a interaction (CRD)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: InteractionResource = BakeryControllerFixtures.interactionResource.copy()
    for {
      _ <- mockDelete[ConfigMap](interaction.name + "-manifest")
      _ <- mockDelete[Service](interaction.name)
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", interaction.name)
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-config")
      _ <- mockDelete[Deployment](interaction.name)
      _ <- mockDeleteAll[ReplicaSetList, ReplicaSet](ReplicaSet.rsListDef, "bakery-interaction-name", interaction.name)
      _ <- mockDeleteAll[PodList, Pod](Pod.poListDef, "bakery-interaction-name", interaction.name)
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.DELETED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyDelete[ConfigMap](interaction.name + "-manifest")
          _ <- verifyDelete[Service](interaction.name)
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-config")
          _ <- verifyDelete[Deployment](interaction.name)
          _ <- verifyDeleteAll[ReplicaSetList](ReplicaSet.rsListDef, "bakery-interaction-name", interaction.name)
          _ <- verifyDeleteAll[PodList](Pod.poListDef, "bakery-interaction-name", interaction.name)
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
        } yield ()
      }
    } yield succeed
  }

  test("creates a interaction (ConfigMap)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: ConfigMap = BakeryControllerFixtures.interactionConfigMapResource.copy()
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    for {
      _ <- mockCreate(Deployment(interaction.name))
      _ <- mockCreate(Service(interaction.name).copy(spec =
        Some(Service.Spec(ports = mockedServicePort))))
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerFixtures.interaction)
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- mockCreate(ConfigMap(interaction.name + "-manifest"))
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.ADDED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyCreate[Deployment](_.name == interaction.name)
          _ <- verifyCreate[Service](_.name == interaction.name)
          _ <- verifyCreate[ConfigMap](_.name == interaction.name + "-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
          _ <- context.remoteInteraction.interfaceWasQueried
        } yield ()
      }
    } yield succeed
  }

  test("updates a interaction (ConfigMap)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: ConfigMap = BakeryControllerFixtures.interactionConfigMapResource.copy()
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    for {
      _ <- mockUpdate(Deployment(interaction.name))
      _ <- mockCreate(Service(interaction.name).copy(spec =
        Some(Service.Spec(ports = mockedServicePort))))
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerFixtures.interaction)
      _ <- mockUpdate[ConfigMap](ConfigMap(interaction.name + "-manifest"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.MODIFIED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.remoteInteraction.interfaceWasQueried
          _ <- verifyUpdate[Deployment](_.name == interaction.name)
          _ <- verifyUpdate[ConfigMap](_.name == interaction.name + "-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
        } yield ()
      }
    } yield succeed
  }

  test("delete a interaction (ConfigMap)") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val interaction: ConfigMap = BakeryControllerFixtures.interactionConfigMapResource.copy()
    for {
      _ <- mockDelete[ConfigMap](interaction.name + "-manifest")
      _ <- mockDelete[Service](interaction.name)
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", interaction.name)
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-config")
      _ <- mockDelete[Deployment](interaction.name)
      _ <- mockDeleteAll[ReplicaSetList, ReplicaSet](ReplicaSet.rsListDef, "bakery-interaction-name", interaction.name)
      _ <- mockDeleteAll[PodList, Pod](Pod.poListDef, "bakery-interaction-name", interaction.name)
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.DELETED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyDelete[ConfigMap](interaction.name + "-manifest")
          _ <- verifyDelete[Service](interaction.name)
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-config")
          _ <- verifyDelete[Deployment](interaction.name)
          _ <- verifyDeleteAll[ReplicaSetList](ReplicaSet.rsListDef, "bakery-interaction-name", interaction.name)
          _ <- verifyDeleteAll[PodList](Pod.poListDef, "bakery-interaction-name", interaction.name)
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
        } yield ()
      }
    } yield succeed
  }

  case class Context(
                      k8s: KubernetesClient,
                      k8sBakerControllerEventStream: K8sEventStream[InteractionResource],
                      k8sBakerControllerEventStream_ConfigMap: K8sEventStream[ConfigMap],
                      configControllerCache: ForceRollingUpdateOnConfigMapUpdate,
                      remoteInteraction: RemoteInteraction,
                      mockServerPort: Int
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
      system <- actorSystemResource
      mockServer <- Resource.make(IO(ClientAndServer.startClientAndServer(0)))(s => IO(s.stop()))
      context <- {
        implicit val s: ActorSystem = system
        implicit val k8s: KubernetesClient = mock[KubernetesClient]
        for {
          eventStream <- K8sEventStream.resource[InteractionResource]
          eventStream_ConfigMap <- K8sEventStream.resource[ConfigMap]
          configControllerCache <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
          _ <- Resource.liftF(mockWatch(eventStream))
          _ <- Resource.liftF(mockWatchForConfigMaps(eventStream_ConfigMap))
          _ <- InteractionController.run(configControllerCache, executionContext)
          _ <- InteractionController.runFromConfigMaps(configControllerCache, executionContext)
        } yield Context(k8s, eventStream, eventStream_ConfigMap, configControllerCache, new RemoteInteraction(mockServer), mockServer.getLocalPort)
      }
    } yield context

  def actorSystemResource: Resource[IO, ActorSystem] =
    Resource.make(IO {
      ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
        """
          |akka {
          |  stdout-loglevel = "OFF"
          |  loglevel = "OFF"
          |}
          |""".stripMargin))
    })((system: ActorSystem) => IO.fromFuture(IO {
      system.terminate().flatMap(_ => system.whenTerminated)
    }).void)

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ScalaTestConfigMap): TestArguments = ()
}
