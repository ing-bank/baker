package com.ing.baker.baas.http

import akka.http.scaladsl.unmarshalling.PredefinedFromEntityUnmarshallers
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.recipe.commonserialize.Recipe
import com.ing.baker.runtime.core.RuntimeEvent

trait BaasMarshalling {
  def kryoUnmarshaller[T] = PredefinedFromEntityUnmarshallers.byteStringUnmarshaller.map { string =>
    val byteArray: Array[Byte] = string.toArray
    kryoPool.fromBytes(byteArray).asInstanceOf[T]
  }

  implicit val addInteractionUnmarshaller = kryoUnmarshaller[AddInteractionHTTPRequest]
  implicit val eventUnmarshaller = kryoUnmarshaller[RuntimeEvent]
  implicit val recipeUnmarshaller = kryoUnmarshaller[Recipe]
}
