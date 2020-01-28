package com.ing.baker.baas.state

import io.kubernetes.client.openapi.apis.CoreV1Api
import io.kubernetes.client.openapi.models.V1Service
import io.kubernetes.client.util.ClientBuilder

import scala.collection.JavaConverters._
import scala.collection.mutable

object KubernetesFunctions {
  val api = new CoreV1Api(ClientBuilder.cluster.build)

  def getInteractionServices(): mutable.Seq[V1Service] = {
    api.listNamespacedService("default", null, null, null, null, null, null, null, null, null)
      .getItems.asScala
  }

  def getInteractionAddresses(): Seq[String] = {
    getInteractionServices().map(_.getMetadata.getName)
  }
}
