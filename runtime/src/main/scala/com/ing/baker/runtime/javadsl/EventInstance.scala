package com.ing.baker.runtime.javadsl

import java.util

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

case class EventInstance(name: String,
                         providedIngredients: util.Map[String, Value])
  extends common.EventInstance with JavaApi {

  def getProvidedIngredients = providedIngredients

  def getName = name

  def this(name0: String) =
    this(name0, java.util.Collections.emptyMap[String, Value])

  def validate(descriptor: EventDescriptor): util.List[String] =
    asScala.validate(descriptor).asJava

  def asScala: scaladsl.EventInstance =
    scaladsl.EventInstance(name, providedIngredients.asScala.toMap)

  def copy(name0: String): EventInstance = {
    new EventInstance(name0, providedIngredients)
  }

  def copy(providedIngredients0: util.Map[String, Value]): EventInstance = {
    new EventInstance(name, providedIngredients0)
  }
}

object EventInstance {
  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def from(event: Any): EventInstance =
    event match {
      case runtimeEvent: EventInstance => runtimeEvent
      case obj =>
        val scalaEvent = scaladsl.EventInstance.unsafeFrom(event)
        new EventInstance(scalaEvent.name, scalaEvent.providedIngredients.asJava)
    }
}
