package com.ing.bakery.clustercontroller.controllers

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.bakery.clustercontroller.controllers.ControllerOperations._
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate.DeploymentTemplateLabelsPatch
import play.api.libs.json.{Format, Json, Writes}
import skuber.api.client.KubernetesClient
import skuber.api.patch.{MetadataPatch, StrategicMergePatch}
import skuber.apps.v1.Deployment
import skuber.json.ext.format.depFormat
import skuber.json.format.{configMapFmt, metadataPatchWrite}
import skuber.{ConfigMap, ObjectResource, ResourceDefinition}

/** Triggers a roll-update on Deployments when chosen ConfigMaps are updated.
  *
  * Kubernetes is able to refresh the mounted files of pods, but a lot of those files are commonly used on boot only,
  * for example configuration files, and for some of those cases it is desired to roll-update the Deployment if the
  * ConfigMaps that are mounted in the Pods get updated. This tool achieves just that, it keeps a cache of such
  * relations between ConfigMaps and Deployments, and when adding a relation this tool will label the ConfigMap
  * so that its Controller can watch for changes, the Controller then will trigger a roll-update on the
  * Deployment if the ConfigMap is changed.
  *
  * For this functionality to work you must call `runController` to start a watch on the ConfigMaps that can trigger a
  * roll-update.
  *
  * The relation are many to many, you can have one ConfigMap related to many Deployments, and one Deployment to many
  * ConfigMaps.
  *
  * Use `watchConfigOf` to add a relation to be watched, then use `stopWatchingConfigOf` to remove a relation or
  * `stopWatchingConfigFor` to remove all relations of a single Deployment.
  *
  * It is possible to directly manipulate the cache without doing Kubernetes operations, all of these methods are
  * suffixed with `NoKubeOp` but it is suggested to use them for tests only.
  *
  * To build this functionality use the `build` method on the companion project.
  *
  * @param cache thread safe mutable map that keeps the relations between configmaps and deployments
  */
final class ForceRollingUpdateOnConfigMapUpdate private (cache: Ref[IO, Map[String, Set[String]]]) {

  def get(configMapName: String): IO[Set[String]] =
    cache.get.map(_.getOrElse(configMapName, Set.empty))

  def getRelatedConfigMaps(deploymentName: String): IO[List[String]] =
    cache.get.map(_.filter(_._2.contains(deploymentName)).keys.toList)

  def watchConfigOf(configMapName: String, deploymentName: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] =
    addComponentConfigWatchLabelTo(configMapName) *> addRelationNoKubeOp(configMapName, deploymentName)

  def stopWatchingConfigOf(configMapName: String, deploymentName: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] = {
    for {
      _ <- removeRelationNoKubeOp(configMapName, deploymentName)
      leftDeployments <- get(configMapName)
      _ <- if (leftDeployments.isEmpty) removeComponentConfigWatchLabelTo(configMapName) else IO.unit
    } yield ()
  }

  def stopWatchingConfigFor(deploymentName: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] =
    for {
      oldConfigMaps <- getRelatedConfigMaps(deploymentName)
      _ <- oldConfigMaps.parTraverse(stopWatchingConfigOf(_, deploymentName))
    } yield ()

  def forceUpdate(deploymentName: String)(implicit cd: ContextShift[IO], k8s: KubernetesClient): IO[Unit] = {
    def patch[D <: ObjectResource](implicit format: Format[D], rd: ResourceDefinition[D]): IO[D] =
      io(k8s.patch[DeploymentTemplateLabelsPatch, D](
        deploymentName,
        DeploymentTemplateLabelsPatch(Map(ForceRollingUpdateOnConfigMapUpdate.componentForceUpdateLabel))))
    attemptOpOrTryOlderVersion(
      v1 = patch[Deployment],
      older = patch[skuber.ext.Deployment]
    ).void
  }

  def addRelationNoKubeOp(configMapName: String, deploymentName: String): IO[Unit] =
    cache.update { entries =>
      val current = entries.getOrElse(configMapName, Set.empty)
      val addedDeployment = current + deploymentName
      entries + (configMapName -> addedDeployment)
    }

  def removeRelationNoKubeOp(configMapName: String, deploymentName: String): IO[Unit] =
    cache.update { entries =>
      entries.get(configMapName).fold(entries) { current =>
        val removedDeployment = current - deploymentName
        if (removedDeployment.isEmpty) entries.-(configMapName)
        else entries + (configMapName -> removedDeployment)
      }
    }

  def removeDeploymentNoKubeOp(deploymentName: String): IO[Unit] =
    cache.update { entries =>
      entries.mapValues(_ - deploymentName)
    }

  def runController(implicit actorSystem: ActorSystem, cs: ContextShift[IO], timer: Timer[IO], k8s: KubernetesClient): Resource[IO, Unit] =
    controller.runController(existsLabelFilter = Some(ForceRollingUpdateOnConfigMapUpdate.COMPONENT_CONFIG_WATCH_LABEL))

  private def addComponentConfigWatchLabelTo(configRef: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] =
    IO.fromFuture(IO(k8s.patch[MetadataPatch, ConfigMap](
      configRef,
      MetadataPatch(labels = Some(Map(ForceRollingUpdateOnConfigMapUpdate.componentConfigWatchLabel)))
    ))).void

  private def removeComponentConfigWatchLabelTo(configRef: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] =
    IO.fromFuture(IO(k8s.patch[MetadataPatch, ConfigMap](
      configRef,
      MetadataPatch(labels = Some(Map(
        "$patch" -> "delete",
        ForceRollingUpdateOnConfigMapUpdate.componentConfigWatchLabel
      )))
    ))).void

  private def controller(implicit actorSystem: ActorSystem, cs: ContextShift[IO], timer: Timer[IO]): ControllerOperations[ConfigMap] =
    new ControllerOperations[ConfigMap] {
      override def create(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] = IO.unit
      override def upgrade(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] =
        for {
          deployments <- get(resource.name)
          _ = logger.info(s"CONFIGMAP UPGRADED ${resource.metadata.name}, related deployments: ${deployments.mkString(", ")}")
          _ <- deployments.toList.traverse(forceUpdate(_)(cs, k8s))
        } yield ()
      override def terminate(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] = IO.unit
    }
}

object ForceRollingUpdateOnConfigMapUpdate {

  val COMPONENT_CONFIG_WATCH_LABEL = "bakery-watch-config"

  val COMPONENT_FORCE_UPDATE_LABEL = "bakery-force-update"

  val componentConfigWatchLabel: (String, String) = COMPONENT_CONFIG_WATCH_LABEL -> ""

  def componentForceUpdateLabel: (String, String) = COMPONENT_FORCE_UPDATE_LABEL -> UUID.randomUUID().toString.take(63)

  def build: IO[ForceRollingUpdateOnConfigMapUpdate] =
    Ref.of[IO, Map[String, Set[String]]](Map.empty).map(new ForceRollingUpdateOnConfigMapUpdate(_))

  case class DeploymentTemplateLabelsPatch(labels: Map[String, String]) extends StrategicMergePatch

  object DeploymentTemplateLabelsPatch {
    implicit val deploymentTemplateLabelsPatchWrites: Writes[DeploymentTemplateLabelsPatch] =
      Writes.apply(patch => Json.obj(
        "spec" -> Json.obj(
          "template" -> Json.obj(
            "metadata" -> Json.obj(
              "labels" -> Json.toJsObject(patch.labels))))))
  }
}
