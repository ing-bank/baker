package com.ing.baker.baas.kubeapi

import scala.io.Source

case class PodPort(name: String, port: Int, targetPort: Either[Int, String], protocol: String = "TCP") {

  def mock: String = Source
    .fromResource("mocks/kubeapi_GET_port.json")
    .mkString
    .replace("{{name}}", name)
    .replace("{{protocol}}", protocol)
    .replace("\"{{port}}\"", port.toString)
    .replace("\"{{targetPort}}\"", targetPort match {
      case Left(portInt) => portInt.toString
      case Right(portString) => s""""$portString""""
    })

}
