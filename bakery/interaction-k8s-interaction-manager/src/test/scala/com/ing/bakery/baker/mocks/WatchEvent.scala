package com.ing.bakery.baker.mocks

import play.api.libs.json.Format

trait WatchEvent {

  type Resource

  def item: Resource

  def fmt: Format[Resource]

  def eventType: WatchEvent.WatchEventType

  override def toString: String =
    s"""{"type": "$eventType", "object": ${fmt.writes(item).toString} }"""
}

object WatchEvent {

  sealed trait WatchEventType
  case object Added extends WatchEventType { override def toString: String = "ADDED" }
  case object Deleted extends WatchEventType { override def toString: String = "DELETED" }
  case object Modified extends WatchEventType { override def toString: String = "MODIFIED" }

  sealed trait ResourcePath
  case object BakersPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/bakers" }
  case object InteractionsPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/interactions" }
}