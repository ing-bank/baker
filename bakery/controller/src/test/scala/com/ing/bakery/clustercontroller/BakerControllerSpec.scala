package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, ForceRollingUpdateOnConfigMapUpdate}
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.mockito.{ArgumentMatchersSugar, MockitoSugar}
import org.scalatest.matchers.should.Matchers
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.api.patch.MetadataPatch
import skuber.apps.v1.{Deployment, ReplicaSet, ReplicaSetList}
import skuber.{ConfigMap, Service}

import scala.concurrent.Future

class BakerControllerSpec extends BakeryFunSpec with Matchers with MockitoSugar with ArgumentMatchersSugar {

  test("creates a baker and adds deployment to the config relationship cache") { context =>
    val baker: BakerResource = BakeryControllerSpec.bakerResource.copy(spec =
      BakeryControllerSpec.bakerResource.spec.copy(config = Some("test-config")))
    doReturn(Future.successful(ConfigMap(baker.name + "-manifest"))).when(context.k8s).create[ConfigMap](*)(*, *, *)
    doReturn(Future.successful(Deployment(baker.name))).when(context.k8s).create[Deployment](*)(*, *, *)
    doReturn(Future.successful(Service(baker.name))).when(context.k8s).create[Service](*)(*, *, *)
    doReturn(Future.successful(ConfigMap("test-config"))).when(context.k8s).patch(
      name = same("test-config"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) => patch.labels.exists(_.contains(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))),
      namespace = same(None)
    )(*, *, *, *)
    for {
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.ADDED, baker))
      _ <- eventually("config relationship cache contains the deployment and config") {
        context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(baker.name)))
      }
    } yield succeed
  }

  test("updates a baker and adds deployment to the config relationship cache") { context =>
    val baker: BakerResource = BakeryControllerSpec.bakerResource.copy(spec =
      BakeryControllerSpec.bakerResource.spec.copy(config = Some("test-config")))
    doReturn(Future.successful(ConfigMap(baker.name + "-manifest"))).when(context.k8s).update[ConfigMap](*)(*, *, *)
    doReturn(Future.successful(Deployment(baker.name))).when(context.k8s).update[Deployment](*)(*, *, *)
    doReturn(Future.successful(ConfigMap("test-config"))).when(context.k8s).patch(
      name = same("test-config"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) => patch.labels.exists(_.contains(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))),
      namespace = same(None)
    )(*, *, *, *)
    for {
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.MODIFIED, baker))
      _ <- eventually("config relationship cache contains the deployment and config") {
        context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(baker.name)))
      }
    } yield succeed
  }

  test("delete a baker and deletes deployment to the config relationship cache") { context =>
    val baker: BakerResource = BakeryControllerSpec.bakerResource.copy(spec =
      BakeryControllerSpec.bakerResource.spec.copy(config = Some("test-config")))
    doReturn(Future.unit).when(context.k8s).delete[ConfigMap](*, *)(*, *)
    doReturn(Future.unit).when(context.k8s).delete[Deployment](*, *)(*, *)
    doReturn(Future.unit).when(context.k8s).delete[Service](*, *)(*, *)
    doReturn(Future.successful(skuber.listResourceFromItems[ReplicaSet](List(ReplicaSet(baker.name))))).when(context.k8s).deleteAllSelected[ReplicaSetList](*)(*, *, *)
    for {
      _ <- context.configControllerCache.addRelationNoKubeOp(baker.name + "-manifest", baker.name)
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", baker.name)
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.DELETED, baker))
      _ <- eventually("config relationship cache contains the deployment and config") {
        context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
      }
    } yield succeed
  }

  case class Context(
    k8s: KubernetesClient,
    k8sBakerControllerEventStream: K8sEventStream[BakerResource],
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
          configControllerCache <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
          _ = doAnswer(eventStream.source).when(k8s).watchAllContinuously(*, *)(*, *, *)
          _ <- BakerController.run(configControllerCache)
        } yield Context(k8s, eventStream, configControllerCache)
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
