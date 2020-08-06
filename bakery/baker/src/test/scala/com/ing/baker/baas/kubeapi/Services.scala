package com.ing.baker.baas.kubeapi

import scala.io.Source

case class Services(items: List[Service]) {

  def ++ (services: Service*): Services =
    Services(items ++ services.toList)

  def mock: List[String] = {
    val eventTemplate = Source.fromResource("mocks/kubeapi_GET_services_watch_event.json").mkString
    items.map { service =>
      eventTemplate
        .replace("\"{{items[kubeapi_GET_service.json]}}\"", service.mock)
    }
  }
}
