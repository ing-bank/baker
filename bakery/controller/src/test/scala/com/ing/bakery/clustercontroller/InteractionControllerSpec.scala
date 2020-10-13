package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.{ForceRollingUpdateOnConfigMapUpdate, InteractionController, InteractionResource}
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.mocks.RemoteInteraction
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.mockito.{ArgumentMatchersSugar, MockitoSugar}
import org.mockserver.integration.ClientAndServer
import org.scalatest.matchers.should.Matchers
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.api.patch.MetadataPatch
import skuber.apps.v1.Deployment
import skuber.{ConfigMap, Service}

import scala.concurrent.Future

class InteractionControllerSpec extends BakeryFunSpec with Matchers with MockitoSugar with ArgumentMatchersSugar {

  test("creates a interaction and adds deployment to the config relationship cache") { context =>
    val interaction: InteractionResource = BakeryControllerSpec.interactionResource.copy(spec =
      BakeryControllerSpec.interactionResource.spec.copy(configMapMounts = Some(List("test-config"))))
    val mockedServicePort = List(Service.Port(name = "http-api", port = context.mockServerPort))
    doReturn(Future.successful(Deployment(interaction.name))).when(context.k8s).create[Deployment](
      argThat((deployment: Deployment) => deployment.name == interaction.name))(*, *, *)
    doReturn(Future.successful(Service(interaction.name).copy(spec =
      Some(Service.Spec(ports = mockedServicePort))))).when(context.k8s).create[Service](
        argThat((service: Service) => service.name == interaction.name))(*, *, *)
    doReturn(Future.successful(ConfigMap("test-config"))).when(context.k8s).patch(
      name = same("test-config"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) => patch.labels.exists(_.contains(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))),
      namespace = same(None)
    )(*, *, *, *)
    doReturn(Future.successful(ConfigMap(interaction.name + "-manifest"))).when(context.k8s).create[ConfigMap](
      argThat[ConfigMap]((map: ConfigMap) => map.name == interaction.name + "-manifest"))(*, *, *)
    for {
      _ <- context.remoteInteraction.publishesItsInterface(BakeryControllerSpec.interaction)
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.ADDED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
          _ <- context.remoteInteraction.interfaceWasQueried(BakeryControllerSpec.interaction)
          _ = verify(context.k8s).create(argThat[ConfigMap]((map: ConfigMap) => map.name == interaction.name + "-manifest"))(*, *, *)
          _ = verify(context.k8s).patch(
            name = same("test-config"),
            patchData = argThat[MetadataPatch]((patch: MetadataPatch) => patch.labels.exists(_.contains(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))),
            namespace = same(None))(*, *, *, *)
        } yield ()
      }
    } yield succeed
  }

  test("updates a interaction and adds deployment to the config relationship cache") { context =>
    val interaction: InteractionResource = BakeryControllerSpec.interactionResource.copy(spec =
      BakeryControllerSpec.interactionResource.spec.copy(configMapMounts = Some(List("test-config"))))
    doReturn(Future.successful(Deployment(interaction.name))).when(context.k8s).update[Deployment](*)(*, *, *)
    doReturn(Future.successful(ConfigMap("test-config"))).when(context.k8s).patch(
      name = same("test-config"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) =>
        patch.labels.contains(Map(
          "$patch" -> "delete",
          ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL -> ""
        ))),
      namespace = same(None)
    )(*, *, *, *)
    doReturn(Future.successful(ConfigMap("test-config"))).when(context.k8s).patch(
      name = same("test-config"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) => patch.labels.exists(_.contains(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))),
      namespace = same(None)
    )(*, *, *, *)
    for {
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.MODIFIED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        for {
          _ <- context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set(interaction.name)))
        } yield ()
      }
    } yield succeed
  }

  /*
  test("delete a interaction and deletes deployment to the config relationship cache") { context =>
    val interaction: InteractionResource = BakeryControllerSpec.interactionResource.copy(spec =
      BakeryControllerSpec.interactionResource.spec.copy(configMapMounts = Some(List("test-config"))))
    doReturn(Future.unit).when(context.k8s).delete[ConfigMap](*, *)(*, *)
    doReturn(Future.unit).when(context.k8s).delete[Deployment](*, *)(*, *)
    doReturn(Future.unit).when(context.k8s).delete[Service](*, *)(*, *)
    doReturn(Future.successful(skuber.listResourceFromItems[ReplicaSet](List(ReplicaSet(interaction.name))))).when(context.k8s).deleteAllSelected[ReplicaSetList](*)(*, *, *)
    doReturn(Future.successful(ConfigMap("RecipeOne-manifest"))).when(context.k8s).patch(
      name = same("RecipeOne-manifest"),
      patchData = argThat[MetadataPatch]((patch: MetadataPatch) =>
        patch.labels.contains(Map(
          "$patch" -> "delete",
          ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL -> ""
        ))),
      namespace = same(None)
    )(*, *, *, *)
    for {
      _ <- context.configControllerCache.addRelationNoKubeOp(interaction.name + "-manifest", interaction.name)
      _ <- context.configControllerCache.addRelationNoKubeOp("test-config", interaction.name)
      _ <- context.k8sBakerControllerEventStream.fire(WatchEvent(EventType.DELETED, interaction))
      _ <- eventually("config relationship cache contains the deployment and config") {
        context.configControllerCache.get("test-config").map(deployments => assert(deployments == Set.empty))
      }
    } yield succeed
  }
   */

  case class Context(
                      k8s: KubernetesClient,
                      k8sBakerControllerEventStream: K8sEventStream[InteractionResource],
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
          configControllerCache <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
          _ = doAnswer(eventStream.source).when(k8s).watchAllContinuously(*, *)(*, *, *)
          _ <- InteractionController.run(configControllerCache, executionContext)
        } yield Context(k8s, eventStream, configControllerCache, new RemoteInteraction(mockServer), mockServer.getLocalPort)
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
