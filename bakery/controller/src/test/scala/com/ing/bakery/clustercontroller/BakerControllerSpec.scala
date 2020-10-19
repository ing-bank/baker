package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, ForceRollingUpdateOnConfigMapUpdate}
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.{ConfigMap, Pod, PodList, Service}

class BakerControllerSpec extends BakeryFunSpec with KubernetesMockito {

  test("creates a baker") { context =>
    val resource: BakerResource = BakeryControllerFixtures.bakerResource.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- mockCreate(ConfigMap("test-recipe-manifest"))
      _ <- mockCreate(Deployment("test-recipe"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-recipe-manifest")
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- mockCreate(Service("test-recipe"))
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.ADDED, resource))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set("test-recipe")))
          _ <- verifyCreate[ConfigMap](_.name == "test-recipe-manifest")
          _ <- verifyCreate[Deployment](_.name == "test-recipe")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-recipe-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- verifyCreate[Service](_.name == "test-recipe")
        } yield ()
      }
    } yield succeed
  }

  test("updates a baker") { context =>
    val baker: BakerResource = BakeryControllerFixtures.bakerResource.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- mockUpdate(ConfigMap("test-recipe-manifest"))
      _ <- mockUpdate(Deployment("test-recipe"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.MODIFIED, baker))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyUpdate[ConfigMap](_.name == "test-recipe-manifest")
          _ <- verifyUpdate[Deployment](_.name == "test-recipe")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set("test-recipe")))
        } yield ()
      }
    } yield succeed
  }

  test("deletes a baker") { context =>
    implicit val k8sMock: KubernetesClient = context.k8s
    val baker: BakerResource = BakeryControllerFixtures.bakerResource.copy()
    for {
      _ <- context.configControllerCache.addRelationNoKubeOp("test-recipe-manifest", "test-recipe")
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-recipe-manifest")
      _ <- mockDelete[ConfigMap]("test-recipe-manifest")
      _ <- mockDelete[Service]("test-recipe")
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", "test-recipe")
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-config")
      _ <- mockDelete[Deployment]("test-recipe")
      _ <- mockDeleteAll[ReplicaSetList, ReplicaSet](ReplicaSet.rsListDef, "bakery-baker-name", "test-recipe")
      _ <- mockDeleteAll[PodList, Pod](Pod.poListDef, "bakery-baker-name", "test-recipe")

      _ <- context.configControllerCache.addRelationNoKubeOp("test-recipe-manifest", "test-recipe")
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", "test-recipe")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.DELETED, baker))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-recipe-manifest")
          _ <- verifyDelete[ConfigMap]("test-recipe-manifest")
          _ <- verifyDelete[Service]("test-recipe")
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-config")
          _ <- verifyDelete[Deployment]("test-recipe")
          _ <- verifyDeleteAll[ReplicaSetList](ReplicaSet.rsListDef, "bakery-baker-name", "test-recipe")
          _ <- verifyDeleteAll[PodList](Pod.poListDef, "bakery-baker-name", "test-recipe")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
        } yield ()
      }
    } yield succeed
  }

  test("creates a baker (ConfigMap)") { context =>
    val resource: ConfigMap = BakeryControllerFixtures.bakerConfigMapResource.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- mockCreate(ConfigMap("test-recipe-manifest"))
      _ <- mockCreate(Deployment("test-recipe"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-recipe-manifest")
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- mockCreate(Service("test-recipe"))
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.ADDED, resource))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set("test-recipe")))
          _ <- verifyCreate[ConfigMap](_.name == "test-recipe-manifest")
          _ <- verifyCreate[Deployment](_.name == "test-recipe")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-recipe-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- verifyCreate[Service](_.name == "test-recipe")
        } yield ()
      }
    } yield succeed
  }

  test("creates a baker with sidecar (ConfigMap)") { context =>
    val resource: ConfigMap = BakeryControllerFixtures.bakerConfigMapResourceSidecar.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- mockCreate(ConfigMap("test-recipe-manifest"))
      _ <- mockCreate(Deployment("test-recipe"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-recipe-manifest")
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- mockCreate(Service("test-recipe"))
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.ADDED, resource))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set("test-recipe")))
          _ <- verifyCreate[ConfigMap](_.name == "test-recipe-manifest")
          _ <- verifyCreate[Deployment](_.name == "test-recipe")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-recipe-manifest")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- verifyCreate[Service](_.name == "test-recipe")
        } yield ()
      }
    } yield succeed
  }

  test("updates a baker (ConfigMap)") { context =>
    val resource: ConfigMap = BakeryControllerFixtures.bakerConfigMapResource.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- mockUpdate(ConfigMap("test-recipe-manifest"))
      _ <- mockUpdate(Deployment("test-recipe"))
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.MODIFIED, resource))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyUpdate[ConfigMap](_.name == "test-recipe-manifest")
          _ <- verifyUpdate[Deployment](_.name == "test-recipe")
          _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set("test-recipe")))
        } yield ()
      }
    } yield succeed
  }

  test("deletes a baker (ConfigMap)") { context =>
    val resource: ConfigMap = BakeryControllerFixtures.bakerConfigMapResource.copy()
    implicit val k8sMock: KubernetesClient = context.k8s
    for {
      _ <- context.configControllerCache.addRelationNoKubeOp("test-recipe-manifest", "test-recipe")
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-recipe-manifest")
      _ <- mockDelete[ConfigMap]("test-recipe-manifest")
      _ <- mockDelete[Service]("test-recipe")
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", "test-recipe")
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-config")
      _ <- mockDelete[Deployment]("test-recipe")
      _ <- mockDeleteAll[ReplicaSetList, ReplicaSet](ReplicaSet.rsListDef, "bakery-baker-name", "test-recipe")
      _ <- mockDeleteAll[PodList, Pod](Pod.poListDef, "bakery-baker-name", "test-recipe")

      _ <- context.configControllerCache.addRelationNoKubeOp("test-recipe-manifest", "test-recipe")
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", "test-recipe")
      _ = validateMockitoUsage()
      _ <- context.k8sBakerControllerEventStream_ConfigMap.fire(WatchEvent(EventType.DELETED, resource))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-recipe-manifest")
          _ <- verifyDelete[ConfigMap]("test-recipe-manifest")
          _ <- verifyDelete[Service]("test-recipe")
          _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-config")
          _ <- verifyDelete[Deployment]("test-recipe")
          _ <- verifyDeleteAll[ReplicaSetList](ReplicaSet.rsListDef, "bakery-baker-name", "test-recipe")
          _ <- verifyDeleteAll[PodList](Pod.poListDef, "bakery-baker-name", "test-recipe")
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
        } yield ()
      }
    } yield succeed
  }


  case class Context(
    k8s: KubernetesClient,
    k8sBakerControllerEventStream: K8sEventStream[BakerResource],
    k8sBakerControllerEventStream_ConfigMap: K8sEventStream[ConfigMap],
    configControllerCache: ForceRollingUpdateOnConfigMapUpdate
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
      context <- {
        implicit val s: ActorSystem = system
        implicit val k8s: KubernetesClient = mock[KubernetesClient]
        for {
          eventStream <- K8sEventStream.resource[BakerResource]
          eventStream_ConfigMap <- K8sEventStream.resource[ConfigMap]
          configControllerCache <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
          _ <- Resource.liftF(mockWatch(eventStream))
          _ <- Resource.liftF(mockWatchForConfigMaps(eventStream_ConfigMap))
          _ <- BakerController.run(configControllerCache)
          _ <- BakerController.runFromConfigMaps(configControllerCache)
        } yield Context(k8s, eventStream, eventStream_ConfigMap, configControllerCache)
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