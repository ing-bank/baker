package com.ing.baker.baas.mocks

import play.api.libs.json.Format
import skuber.Service

case class WatchEvent[O](item: O, tpe: WatchEvent.WatchEventType)(implicit fmt: Format[O]) {

  override def toString: String =
    s"""{"type": "$tpe", "object": "${fmt.writes(item).toString}" }"""
}

object WatchEvent {

  def ofInteractionService(mock: org.mockserver.integration.ClientAndServer): Service =
    Service(name = "localhost")
      .setPort(Service.Port(
        name = "http-api",
        port = mock.getLocalPort
      ))
      .addLabel("baas-component" -> "remote-interaction")

  sealed trait WatchEventType
  case object Added extends WatchEventType { override def toString: String = "ADDED" }
  case object Deleted extends WatchEventType { override def toString: String = "DELETED" }
  case object Modified extends WatchEventType { override def toString: String = "MODIFIED" }

  sealed trait ResourcePath
  case object BakersPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/bakers" }
  case object InteractionsPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/interactions" }
}