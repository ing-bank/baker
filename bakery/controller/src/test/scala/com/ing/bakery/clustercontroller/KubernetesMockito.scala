package com.ing.bakery.clustercontroller

import cats.effect.IO
import com.ing.bakery.clustercontroller.controllers.ForceRollingUpdateOnConfigMapUpdate.{COMPONENT_FORCE_UPDATE_LABEL, DeploymentTemplateLabelsPatch, componentConfigWatchLabel}
import com.ing.bakery.helpers.K8sEventStream
import org.mockito.{ArgumentMatchersSugar, Mockito, MockitoSugar}
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.api.patch.MetadataPatch
import skuber.apps.v1.Deployment
import skuber.json.format.{configMapFmt, metadataPatchWrite}
import skuber.{ConfigMap, LabelSelector, ListResource, ObjectResource, ResourceDefinition}

import scala.concurrent.Future

trait KubernetesMockito extends MockitoSugar with ArgumentMatchersSugar {

  def mockWatch[O <: ObjectResource](eventStream: K8sEventStream[O])(implicit k8s: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    doAnswer(eventStream.source).when(k8s).watchAllContinuously(*, *)(*, same(rd), *)
  }

  def mockWatchForConfigMaps(eventStream: K8sEventStream[ConfigMap])(implicit k8s: KubernetesClient): IO[Unit] = IO {
    doAnswer(eventStream.source).when(k8s).watchWithOptions(*, *)(*, same(ConfigMap.configMapDef), *)
  }

  def mockCreate[O <: ObjectResource](resource: O)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    Mockito.validateMockitoUsage()
    doReturn(Future.successful(resource)).when(k8sMock).create[O](argThat[O]((o: O) => o.name == resource.name))(*, *, *)
  }

  def verifyCreate[O <: ObjectResource](f: O => Boolean)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    verify(k8sMock).create[O](argThat[O]((o: O) => f(o)))(*, *, *)
  }

  def mockUpdate[O <: ObjectResource](resource: O)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    doReturn(Future.successful(resource)).when(k8sMock).update[O](argThat[O]((o: O) => o.name == resource.name))(*, *, *)
  }

  def verifyUpdate[O <: ObjectResource](f: O => Boolean)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    verify(k8sMock).update[O](argThat[O]((o: O) => f(o)))(*, *, *)
  }

  def mockDelete[O <: ObjectResource](name: String)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    doReturn(Future.unit).when(k8sMock).delete[O](argThat((n: String) => n == name), *)(argThat((rd0: ResourceDefinition[O]) => rd0.spec.names.singular == rd.spec.names.singular), *)
  }

  def verifyDelete[O <: ObjectResource](name: String)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[O]): IO[Unit] = IO {
    verify(k8sMock).delete[O](argThat((n: String) => n == name), *)(argThat((rd0: ResourceDefinition[O]) => rd0.spec.names.singular == rd.spec.names.singular), *)
  }

  def mockDeleteAll[L <: ListResource[_], K <: ObjectResource](rdList: ResourceDefinition[L], labelKey: String, labelValue: String)(implicit k8sMock: KubernetesClient, rd: ResourceDefinition[K]): IO[Unit] = IO {
    doReturn(Future.successful(skuber.listResourceFromItems[K](List.empty))).when(k8sMock).deleteAllSelected[L](
      argThat((selector: LabelSelector) => selector.requirements.contains(IsEqualRequirement(labelKey, labelValue)))
    )(*, same(rdList), *)
  }

  def verifyDeleteAll[L <: ListResource[_]](rdList: ResourceDefinition[L], labelKey: String, labelValue: String)(implicit k8sMock: KubernetesClient): IO[Unit] = IO {
    verify(k8sMock).deleteAllSelected[L](
      argThat((selector: LabelSelector) => selector.requirements.contains(IsEqualRequirement(labelKey, labelValue)))
    )(*, same(rdList), *)
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
