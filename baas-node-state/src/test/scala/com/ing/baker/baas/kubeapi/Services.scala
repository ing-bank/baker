package com.ing.baker.baas.kubeapi

import scala.io.Source

case class Services(items: List[Service]) {

  def ++ (services: Service*): Services =
    Services(items ++ services.toList)

  def mock: String = Source
    .fromResource("mocks/kubeapi_GET_services.json")
    .mkString
    .replace("\"{{items[kubeapi_GET_service.json]}}\"", items.map(_.mock).mkString("[ ", ", ", " ]"))
}
