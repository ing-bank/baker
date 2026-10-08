package com.ing.bakery.kubeapi

import scala.io.Source

case class Service(metadata_name: String, metadata_labels: Map[String, String], spec_ports: List[PodPort], spec_selector: Map[String, String] = Map("app" -> "mock")) {

  def mock: String = Source
    .fromResource("mocks/kubeapi_GET_service.json")
    .mkString
    .replace("{{metadata.name}}", metadata_name)
    .replace("\"{{metadata.labels{}}}\"", TextUtils.mkJsonString(metadata_labels))
    .replace("\"{{spec.ports[kubeapi_GET_port.json]}}\"", spec_ports.map(_.mock).mkString("[ ", ", ", " ]"))
    .replace("\"{{spec.selector{}}}\"", TextUtils.mkJsonString(spec_selector))
}
