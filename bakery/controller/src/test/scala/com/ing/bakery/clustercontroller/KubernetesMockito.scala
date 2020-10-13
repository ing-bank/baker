package com.ing.bakery.clustercontroller

import cats.effect.IO
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate.{COMPONENT_FORCE_UPDATE_LABEL, DeploymentTemplateLabelsPatch, componentConfigWatchLabel}
import org.mockito.{ArgumentMatchersSugar, MockitoSugar}
import play.api.libs.json.Format
import skuber.{ConfigMap, ObjectResource, ResourceDefinition}
import skuber.api.client.KubernetesClient
import skuber.api.patch.MetadataPatch
import skuber.apps.v1.Deployment
import skuber.json.format.{configMapFmt, metadataPatchWrite}

import scala.concurrent.Future

trait KubernetesMockito extends MockitoSugar with ArgumentMatchersSugar {

  def mockCreate[O <: ObjectResource](resource: O)(implicit k8sMock: KubernetesClient, fmt: Format[O], rd: ResourceDefinition[O]): IO[Unit] = IO {
    doReturn(Future.successful(resource)).when(k8sMock).create[O](argThat[O]((o: O) => o.name == resource.name))(same(fmt), same(rd), *)
  }

  def verifyCreate[O <: ObjectResource](f: O => Boolean)(implicit k8sMock: KubernetesClient, fmt: Format[O], rd: ResourceDefinition[O]): IO[Unit] = IO {
    verify(k8sMock).create[O](argThat[O]((o: O) => f(o)))(same(fmt), same(rd), *)
  }

  def mockUpdate[O <: ObjectResource](resource: O)(implicit k8sMock: KubernetesClient, fmt: Format[O], rd: ResourceDefinition[O]): IO[Unit] = IO {
    doReturn(Future.successful(resource)).when(k8sMock).update[O](argThat[O]((o: O) => o.name == resource.name))(same(fmt), same(rd), *)
  }

  def verifyUpdate[O <: ObjectResource](f: O => Boolean)(implicit k8sMock: KubernetesClient, fmt: Format[O], rd: ResourceDefinition[O]): IO[Unit] = IO {
    verify(k8sMock).update[O](argThat[O]((o: O) => f(o)))(same(fmt), same(rd), *)
  }

  def mockPatchingOfConfigMapWatchLabel(configMapName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    doReturn(Future.successful(ConfigMap(configMapName))).when(k8sMock).patch(
      argThat((name: String) => name == configMapName),
      argThat((patch: MetadataPatch) =>
        patch.labels.contains(Map(componentConfigWatchLabel))),
      *
    )(*, *, *, *)
  }

  def verifyPatchingOfConfigMapWatchLabel(configMapName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    verify(k8sMock).patch(
      argThat((name: String) => name == configMapName),
      argThat((patch: MetadataPatch) =>
        patch.labels.contains(Map(componentConfigWatchLabel))),
      same(None)
    )(same(metadataPatchWrite), same(configMapFmt), same(ConfigMap.configMapDef), *)
  }

  def mockPatchingOfRemovingConfigMapWatchLabel(configMapName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    doReturn(Future.successful(ConfigMap(configMapName))).when(k8sMock).patch(
      argThat((name: String) => name == configMapName),
      argThat((patch: MetadataPatch) =>
        patch.labels.contains(Map("$patch" -> "delete", componentConfigWatchLabel))),
      same(None)
    )(*, *, *, *)
  }

  def verifyPatchingOfRemovingConfigMapWatchLabel(configMapName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    verify(k8sMock).patch(
      argThat((name: String) => name == configMapName),
      argThat((patch: MetadataPatch) =>
        patch.labels.contains(Map("$patch" -> "delete", componentConfigWatchLabel))),
      same(None)
    )(*, *, *, *)
  }

  def mockPatchingOfForceRollUpdateLabel(deploymentName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    doReturn(Future.successful(Deployment(deploymentName))).when(k8sMock).patch(
      argThat((name: String) => name == deploymentName),
      argThat((patch: DeploymentTemplateLabelsPatch) =>
        patch.labels.contains(COMPONENT_FORCE_UPDATE_LABEL)),
      same(None)
    )(*, *, *, *)
  }

  def verifyPatchingOfForceRollUpdateLabel(deploymentName: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    verify(k8sMock).patch(
      argThat((name: String) => name == deploymentName),
      argThat((patch: DeploymentTemplateLabelsPatch) =>
        patch.labels.contains(COMPONENT_FORCE_UPDATE_LABEL)),
      same(None)
    )(*, *, *, *)
  }
}
