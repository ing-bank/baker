package com.ing.bakery.clustercontroller

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL
import com.ing.bakery.helpers.K8sEventStream
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.scalatest.{ConfigMap => ScalaTestConfigMap}
import skuber.api.client.{EventType, KubernetesClient, WatchEvent}
import skuber.{ConfigMap, ListOptions}

class ForceRollingUpdateOnConfigMapUpdateSpec extends BakeryFunSpec with KubernetesMockito {

  test("controller forces update on deployments that are within the cache") { context =>
    implicit val k8s: KubernetesClient = context.k8s
    for {
      _ <- context.configWatch.addRelationNoKubeOp("test-config", "test-deployment")
      _ <- mockPatchingOfForceRollUpdateLabel("test-deployment")
      _ <- context.k8sComponentConfigControllerEventStream.fire(WatchEvent(EventType.MODIFIED, ConfigMap("test-config")))
      _ <- eventually("patch was called on k8s client")(verifyPatchingOfForceRollUpdateLabel("test-deployment"))
    } yield succeed
  }

  test("labels config maps when adding a relation between a config map and a deployment to the cache") { context =>
    implicit val k8s: KubernetesClient = context.k8s
    for {
      _ <- mockPatchingOfConfigMapWatchLabel("test-config")
      _ <- context.configWatch.watchConfigOf("test-config", "test-deployment")
      cacheDeployments <- context.configWatch.get("test-config")
      _ <- verifyPatchingOfConfigMapWatchLabel("test-config")
    } yield assert(cacheDeployments.contains("test-deployment"))
  }

  test("un-labels config maps when removing all related deployments from the cache") { context =>
    implicit val k8s: KubernetesClient = context.k8s
    for {
      _ <- mockPatchingOfRemovingConfigMapWatchLabel("test-config")
      _ <- context.configWatch.addRelationNoKubeOp("test-config", "test-deployment")
      _ <- context.configWatch.stopWatchingConfigFor("test-deployment")
      cacheDeployments <- context.configWatch.get("test-config")
      _ <- verifyPatchingOfRemovingConfigMapWatchLabel("test-config")
    } yield assert(cacheDeployments.isEmpty)
  }

  case class Context(
                      k8s: KubernetesClient,
                      k8sComponentConfigControllerEventStream: K8sEventStream[ConfigMap],
                      configWatch: ForceRollingUpdateOnConfigMapUpdate
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
          eventStream <- K8sEventStream.resource[ConfigMap]
          isFilteringOnWatchLabel = (options: ListOptions) =>
            options.labelSelector
              .exists(_.requirements.exists(_.key == COMPONENT_CONFIG_WATCH_LABEL))
          _ = doAnswer(eventStream.source).when(k8s).watchWithOptions(argThat[ListOptions](f = isFilteringOnWatchLabel), *)(*, *, *)
          configControllerCache <- Resource.liftF(ForceRollingUpdateOnConfigMapUpdate.build)
          _ <- configControllerCache.runController
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
