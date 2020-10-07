package com.ing.bakery.clustercontroller.controllers

import java.util.UUID

import akka.actor.ActorSystem
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.bakery.clustercontroller.controllers.ControllerOperations._
import play.api.libs.json.{Format, Json, Writes}
import skuber.api.client.KubernetesClient
import skuber.api.patch.{MetadataPatch, StrategicMergePatch}
import skuber.apps.v1.Deployment
import skuber.json.ext.format.depFormat
import skuber.json.format.{configMapFmt, metadataPatchWrite}
import skuber.{ConfigMap, ObjectResource, ResourceDefinition}
import ControllerOperations._
import scala.concurrent.Future
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate.DeploymentTemplateLabelsPatch

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

final class ForceRollingUpdateOnConfigMapUpdate(cache: Ref[IO, Map[String, Set[String]]]) {

  def get(configMapName: String): IO[Set[String]] =
    cache.get.map(_.getOrElse(configMapName, Set.empty))

  def watchConfigOf(configMapName: String, deploymentName: String)(implicit cs: ContextShift[IO], k8s: KubernetesClient): IO[Unit] =
    addComponentConfigWatchLabelTo(configMapName) *> addRelationNoKubeOp(configMapName, deploymentName)

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

  private def controller(implicit actorSystem: ActorSystem, cs: ContextShift[IO], timer: Timer[IO]): ControllerOperations[ConfigMap] =
    new ControllerOperations[ConfigMap] {
      override def create(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] = IO.unit
      override def upgrade(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] =
        for {
          deployments <- get(resource.name)
          _ = logger.info(s"CONFIGMAP UPGRADED ${resource.metadata.name}, related deployments: ${deployments.mkString(", ")}")
          _ <- deployments.toList.traverse(forceUpdate(_)(k8s))
        } yield ()
      override def terminate(resource: ConfigMap)(implicit k8s: KubernetesClient): IO[Unit] = IO.unit

      private def forceUpdate(deploymentName: String)(implicit k8s: KubernetesClient): IO[Unit] = {
        def patch[D <: ObjectResource](implicit format: Format[D], rd: ResourceDefinition[D]): IO[D] =
          io(k8s.patch[DeploymentTemplateLabelsPatch, D](
            deploymentName,
            DeploymentTemplateLabelsPatch(Map(ForceRollingUpdateOnConfigMapUpdate.componentForceUpdateLabel))))
        attemptOpOrTryOlderVersion(
          v1 = patch[Deployment],
          older = patch[skuber.ext.Deployment]
        ).void
      }
    }
}
