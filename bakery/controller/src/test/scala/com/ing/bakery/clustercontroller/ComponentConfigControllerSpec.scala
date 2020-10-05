package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.ComponentConfigController
import com.ing.bakery.clustercontroller.controllers.ComponentConfigController.{ConfigMapDeploymentRelationCache, DeploymentTemplateLabelsPatch}
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.mockito.{ArgumentMatchersSugar, MockitoSugar}
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.{ConfigMap, LabelSelector, ListOptions}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.apps.Deployment

import scala.concurrent.Future

class ComponentConfigControllerSpec extends BakeryFunSpec with MockitoSugar with ArgumentMatchersSugar {

  test("forces update on deployments that are within the cache") { context =>
    for {
      _ <- context.configControllerCache.add("test-config", "test-deployment")
      _ = doReturn(Future.successful(Deployment("test-deployment"))).when(context.k8s).patch(*, *, *)(*, *, *, *)
      _ <- context.k8sComponentConfigControllerEventStream.fire(WatchEvent(EventType.MODIFIED, ConfigMap("test-config")))
      _ <- eventually("patch was called on k8s client")(IO {
        verify(context.k8s).patch(
          name = same("test-deployment"),
          patchData = argThat[DeploymentTemplateLabelsPatch]((patch: DeploymentTemplateLabelsPatch) => patch.labels.contains(ComponentConfigController.COMPONENT_FORCE_UPDATE_LABEL)),
          namespace = same(None))(*, *, *, *)
      })
    } yield succeed
  }

  case class Context(
    k8s: KubernetesClient,
    k8sComponentConfigControllerEventStream: K8sEventStream[ConfigMap],
    configControllerCache: ConfigMapDeploymentRelationCache
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
        val k8s: KubernetesClient = mock[KubernetesClient]
        for {
          eventStream <- K8sEventStream.resource[ConfigMap]
          isFilteringOnWatchLabel = (options: ListOptions) =>
            options.labelSelector
              .exists(_.requirements.exists(_.key == ComponentConfigController.COMPONENT_CONFIG_WATCH_LABEL))
          _ = doAnswer(eventStream.source).when(k8s).watchWithOptions(argThat[ListOptions](f = isFilteringOnWatchLabel), *)(*, *, *)
          configControllerCache <- ComponentConfigController.resource(k8s)
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
