package com.ing.baker.baas.state

import io.kubernetes.client.openapi.apis.CoreV1Api
import io.kubernetes.client.openapi.models.V1Pod

import scala.collection.mutable

object KubernetesFunctions {

  def setupKubernetesClient: Unit = {
    import io.kubernetes.client.openapi.Configuration
    import io.kubernetes.client.util.ClientBuilder
    // loading the in-cluster config, including:// loading the in-cluster config, including:
    //   1. service-account CA
    //   2. service-account bearer-token
    //   3. service-account namespace
    //   4. master endpoints(ip, port) from pre-set environment variables
    val client = ClientBuilder.cluster.build

    // set the global default api-client to the in-cluster one from above
    Configuration.setDefaultApiClient(client)
  }

  def getInteractionPods(): mutable.Seq[V1Pod] = {
    // the CoreV1Api loads default api-client from global configuration.
    val api = new CoreV1Api

    import scala.collection.JavaConverters._

    api.listNamespacedPod("default", null, null, null, null, null, null, null, null, null)
      .getItems.asScala
      .filter(isRunningInteractions)
  }

  private def isRunningInteractions(pod: V1Pod): Boolean = {
    pod.getStatus.getPhase.equals("Running") &&
      pod.getMetadata.getLabels.getOrDefault("baas-component", "NOTAVAILABLE").equals("remote-interaction")
  }
}
