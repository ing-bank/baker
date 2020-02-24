package com.ing.baker.baas.state

import io.kubernetes.client.openapi.ApiClient
import io.kubernetes.client.openapi.apis.CoreV1Api
import io.kubernetes.client.openapi.models.V1Service
import io.kubernetes.client.util.ClientBuilder

import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.concurrent.Future

class ServiceDiscoveryKubernetes(namespace: String, client: ApiClient = ClientBuilder.cluster.build) extends  ServiceDiscovery {

  private val api = new CoreV1Api(client)

  def getInteractionAddresses: Future[Seq[String]] = {
    Future.successful(getInteractionServices().map(service => "http://" + service.getMetadata.getName + ":" + service.getSpec.getPorts.asScala.head.getPort))
  }

  def getEventListenersAddresses: Future[Seq[(String, String)]] = {
    Future.successful(getEventListenerServices().map { service =>
      (service.getMetadata.getLabels.getOrDefault("baker-recipe", "All-Recipes"), "http://" + service.getMetadata.getName + ":" +  + service.getSpec.getPorts.asScala.head.getPort)
    })
  }

  override def getBakerEventListenersAddresses: Future[Seq[String]] = {
    Future.successful(getBakerEventListenerServices().map { service =>
      "http://" + service.getMetadata.getName + ":8080"
    })
  }

  private def getInteractionServices(): mutable.Seq[V1Service] = {
    api.listNamespacedService(namespace, null, null, null, null, null, null, null, null, null)
      .getItems
      .asScala
      .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
        .equals("remote-interaction"))
  }

  private def getEventListenerServices(): mutable.Seq[V1Service] = {
    api.listNamespacedService(namespace, null, null, null, null, null, null, null, null, null)
      .getItems
      .asScala
      .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
        .equals("remote-event-listener"))
  }

  private def getBakerEventListenerServices(): mutable.Seq[V1Service] = {
    api.listNamespacedService(namespace, null, null, null, null, null, null, null, null, null)
      .getItems
      .asScala
      .filter(_.getMetadata.getLabels.getOrDefault("baas-component", "Wrong")
        .equals("remote-baker-event-listener"))
  }
}

