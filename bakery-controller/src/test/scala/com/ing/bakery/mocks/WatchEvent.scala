package com.ing.bakery.mocks

import com.ing.bakery.clustercontroller.ops.{BakerResource, InteractionResource}
import play.api.libs.json.Format
import skuber.{ObjectResource, ResourceDefinition}

case class WatchEvent[O <: ObjectResource](item: O, tpe: WatchEvent.WatchEventType)(implicit fmt: Format[O], rd: ResourceDefinition[O]) {

  override def toString: String =
    s"""{"type": "$tpe", "object": "${fmt.writes(item).toString}" }"""
}

object WatchEvent {

  val recipeResource: BakerResource =
    BakerResource(spec = BakerResource.Spec(
      bakeryVersion = "3.0.2-SNAPSHOT",
      replicas = 2,
      recipes = List("Cg9JdGVtUmVzZXJ2YXRpb24S5gYKoANinQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhQaEghkEQAAAAAAAABAGJsBIMDPJAoWChQKEHVuYXZhaWxhYmxlSXRlbXMQAQoTChEKDXJlc2VydmVkSXRlbXMQAQoLCgkKBWl0ZW1zEAEKUFpOCkoKC09yZGVyUGxhY2VkEhwKB29yZGVySWQSESIPCg0KB29yZGVySWQSAggREh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERABCkpaSApEChhPcmRlckhhZFVuYXZhaWxhYmxlSXRlbXMSKAoQdW5hdmFpbGFibGVJdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEQAApVWlMKTwoNSXRlbXNSZXNlcnZlZBI+Cg1yZXNlcnZlZEl0ZW1zEi0iKwodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYQAAoSChAKDFJlc2VydmVJdGVtcxACCg0KCwoHb3JkZXJJZBABEgYIAxAAGAESIAgHEAUYASIYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEhUIBxAGGAEiDUl0ZW1zUmVzZXJ2ZWQSBggGEAIYARIGCAUQARgBEgYIBBAIGAESBggEEAMYARIGCAAQBxgBEgYICBAAGAE6EDc5Yzg5MDg2NjIzOGNmNGI=")
    ))

  val ineractionResource: InteractionResource =
    InteractionResource(spec = InteractionResource.Spec(
      image = "my-image",
      replicas = 1,
      env = List.empty,
      configMapMounts = List.empty,
      secretMounts = List.empty
    ))

  sealed trait WatchEventType
  case object Added extends WatchEventType { override def toString: String = "ADDED" }
  case object Deleted extends WatchEventType { override def toString: String = "DELETED" }
  case object Modified extends WatchEventType { override def toString: String = "MODIFIED" }

  sealed trait ResourcePath
  case object BakersPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/bakers" }
  case object InteractionsPath extends ResourcePath { override def toString: String = "/apis/ing-bank.github.io/v1/namespaces/default/interactions" }
}
