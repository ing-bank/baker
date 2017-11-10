package com.ing.baker.baas.http

import akka.http.scaladsl.unmarshalling.PredefinedFromEntityUnmarshallers
import akka.http.scaladsl.marshalling.PredefinedToEntityMarshallers
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.recipe.commonserialize.Recipe
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent, SensoryEventStatus}

import scala.reflect.ClassTag

trait BaasMarshalling {

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
  implicit val processStateMarhaller = kryoMarhaller[ProcessState]
}
