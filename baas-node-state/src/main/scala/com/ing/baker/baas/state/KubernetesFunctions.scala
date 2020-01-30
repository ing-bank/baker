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
      .getItems
      .asScala
      .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
        .equals("remote-interaction"))
  }

  def getInteractionAddresses(): Seq[String] = {
    getInteractionServices().map("http://" + _.getMetadata.getName + ":8080")
  }

  def getEventListenerServices(): mutable.Seq[V1Service] = {
    api.listNamespacedService("default", null, null, null, null, null, null, null, null, null)
      .getItems
      .asScala
      .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
        .equals("remote-event-listener"))
  }

  def getEventListenersAddresses(): Seq[(String, String)] = {
    getEventListenerServices().map { service =>
      (service.getMetadata.getLabels.getOrDefault("baker-recipe", "Wrong"), "http://" + service.getMetadata.getName + ":8080")
    }
  }

}
