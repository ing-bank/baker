package com.ing.baker.baas.mocks

import play.api.libs.json.Format
import skuber.Service

trait WatchEvent {

  type Resource

  def item: Resource

  def fmt: Format[Resource]

  def eventType: WatchEvent.WatchEventType

  override def toString: String =
    s"""{"type": "$eventType", "object": ${fmt.writes(item).toString} }"""
}

object WatchEvent {

  def ofInteractionService(port: Int, tpe: WatchEventType): WatchEvent =
    new WatchEvent {
      override type Resource = Service

      override def item: Resource =
        Service(name = "localhost")
          .setPort(Service.Port(
            name = "http-api",
            port = port
          ))
          .addLabel("baas-component" -> "remote-interaction")

      override def fmt: Format[Resource] =
        skuber.json.format.serviceFmt

      override def eventType: WatchEventType =
        tpe
    }

  sealed trait WatchEventType
  case object Added extends WatchEventType { override def toString: String = "ADDED" }
  case object Deleted extends WatchEventType { override def toString: String = "DELETED" }
  case object Modified extends WatchEventType { override def toString: String = "MODIFIED" }

  sealed trait ResourcePath
  case object BakersPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/bakers" }
  case object InteractionsPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/interactions" }
}