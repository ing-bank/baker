package com.ing.bakery.mocks

import play.api.libs.json.Format
import skuber.ObjectResource

trait WatchEvent {

  type Resource

  def item: Resource

  def fmt: Format[Resource]

  def eventType: WatchEvent.WatchEventType

  override def toString: String =
    s"""{"type": "$eventType", "object": ${fmt.writes(item).toString} }"""
}

object WatchEvent {

  def of[O <: ObjectResource](resource: O, tpe: WatchEventType)(implicit _fmt: Format[O]): WatchEvent =
    new WatchEvent {
      override type Resource = O
      override def item: Resource = resource
      override def fmt: Format[Resource] = _fmt
      override def eventType: WatchEventType = tpe
    }

  sealed trait WatchEventType
  object WatchEventType {
    case object Added extends WatchEventType { override def toString: String = "ADDED" }
    case object Deleted extends WatchEventType { override def toString: String = "DELETED" }
    case object Modified extends WatchEventType { override def toString: String = "MODIFIED" }
  }

  sealed trait ResourcePath
  object ResourcePath {
    case object BakersPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/bakers" }
    case object InteractionsPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/interactions" }
    case object DeploymentsPath extends ResourcePath { override def toString: String = "/apis/extensions/v1beta1/namespaces/default/deployments" }
    case object ServicesPath extends ResourcePath { override def toString: String = "/api/v1/namespaces/default/services" }
  }
}
