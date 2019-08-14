package com.ing.baker.baas.http

import akka.http.scaladsl.marshalling.PredefinedToEntityMarshallers
import akka.http.scaladsl.unmarshalling.PredefinedFromEntityUnmarshallers
import com.ing.baker.baas.KryoUtil
import com.ing.baker.recipe.common.Recipe
import com.ing.baker.runtime.core.{RuntimeEvent, SensoryEventStatus}
import com.twitter.chill.KryoPool

import scala.reflect.ClassTag

trait BaasMarshalling {

  val kryoPool: KryoPool = KryoUtil.defaultKryoPool

  def kryoUnmarshaller[T] = PredefinedFromEntityUnmarshallers.byteStringUnmarshaller.map { string =>
    val byteArray: Array[Byte] = string.toArray
    kryoPool.fromBytes(byteArray).asInstanceOf[T]
  }

  def kryoMarhaller[T: ClassTag] = PredefinedToEntityMarshallers.ByteArrayMarshaller.compose[T] { obj =>
    kryoPool.toBytesWithClass(obj)
  }

  implicit val addInteractionUnmarshaller = kryoUnmarshaller[AddInteractionHTTPRequest]
  implicit val eventUnmarshaller = kryoUnmarshaller[RuntimeEvent]
  implicit val recipeUnmarshaller = kryoUnmarshaller[Recipe]

  implicit val sensoryEventStatusMarhaller = kryoMarhaller[SensoryEventStatus]
  implicit val ingredientsMarhaller = kryoMarhaller[Map[String, Any]]
  implicit val eventMarshaller = kryoMarhaller[RuntimeEvent]
  implicit val eventListMarshaller = kryoMarhaller[List[RuntimeEvent]]
  implicit val stringMarshaller = kryoMarhaller[String]
}
