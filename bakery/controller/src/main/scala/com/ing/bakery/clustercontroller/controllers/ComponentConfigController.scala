package com.ing.bakery.clustercontroller.controllers

import java.util.UUID

import cats.implicits._
import akka.actor.ActorSystem
import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.bakery.clustercontroller.controllers.ComponentConfigController._
import com.typesafe.scalalogging.LazyLogging
import play.api.libs.json.{Json, Writes}
import skuber.ConfigMap
import skuber.api.client.KubernetesClient
import skuber.api.patch.{MetadataPatch, StrategicMergePatch}
import skuber.apps.v1.Deployment
import skuber.json.format.metadataPatchWrite
import skuber.json.format.configMapFmt

object ComponentConfigController {

  val COMPONENT_CONFIG_WATCH_LABEL = "bakery-watch-config"

  val COMPONENT_FORCE_UPDATE_LABEL = "bakery-force-update"

  def componentForceUpdateLabel: (String, String) = COMPONENT_FORCE_UPDATE_LABEL -> UUID.randomUUID().toString.take(63)

  def run(k8s: KubernetesClient)(implicit actorSystem: ActorSystem, cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, ConfigMapDeploymentRelationCache] =
    for {
      cache <- Resource.liftF(ConfigMapDeploymentRelationCache.build)
      _ <- new ComponentConfigController(cache).watch(k8s, existsLabel = Some(COMPONENT_CONFIG_WATCH_LABEL))
    } yield cache

  def addComponentConfigWatchLabel(k8s: KubernetesClient, configRef: Option[String])(implicit cs: ContextShift[IO]): IO[Unit] = {
    configRef.fold(IO.unit) { configMapName =>
      IO.fromFuture(IO(k8s.patch[MetadataPatch, ConfigMap](
        configMapName,
        MetadataPatch(labels = Some(Map(COMPONENT_CONFIG_WATCH_LABEL -> "")))
      ))).void
    }
  }

  final class ConfigMapDeploymentRelationCache(cache: Ref[IO, Map[String, Set[String]]]) {

    def get(configMapName: String): IO[Set[String]] =
      cache.get.map(_.getOrElse(configMapName, Set.empty))

    def add(configMapName: String, deploymentName: String): IO[Unit] =
      cache.update { entries =>
        val current = entries.getOrElse(configMapName, Set.empty)
        val addedDeployment = current + deploymentName
        entries + (configMapName -> addedDeployment)
      }

    def remove(configMapName: String, deploymentName: String): IO[Unit] =
      cache.update { entries =>
        entries.get(configMapName).fold(entries) { current =>
          val removedDeployment = current - deploymentName
          if (removedDeployment.isEmpty) entries.-(configMapName)
          else entries + (configMapName -> removedDeployment)
        }
      }

    def removeDeployment(deploymentName: String): IO[Unit] =
      cache.update { entries =>
        entries.mapValues(_ - deploymentName)
      }
  }

  object ConfigMapDeploymentRelationCache {

    def build: IO[ConfigMapDeploymentRelationCache] =
      Ref.of[IO, Map[String, Set[String]]](Map.empty).map(new ConfigMapDeploymentRelationCache(_))
  }

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

final class ComponentConfigController(configCache: ConfigMapDeploymentRelationCache)(implicit cs: ContextShift[IO], timer: Timer[IO]) extends ControllerOperations[ConfigMap] with LazyLogging  {

  override def create(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
    IO.unit

  override def upgrade(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
    for {
      deployments <- configCache.get(resource.name)
      _ = logger.info(s"CONFIGMAP UPGRADED ${resource.metadata.name}, related deployments: ${deployments.mkString(", ")}")
      _ <- deployments.toList.traverse(forceUpdate(k8s, _))
    } yield ()

  override def terminate(resource: ConfigMap, k8s: KubernetesClient): IO[Unit] =
    IO.unit

  private def forceUpdate(k8s: KubernetesClient, deploymentName: String): IO[Unit] = {
    IO.fromFuture(IO {
      k8s.patch[ComponentConfigController.DeploymentTemplateLabelsPatch, Deployment](
        deploymentName,
        DeploymentTemplateLabelsPatch(Map(ComponentConfigController.componentForceUpdateLabel)))
    }).map { dep =>
      logger.info(dep.toString)
      dep
    }.void
  }
}
