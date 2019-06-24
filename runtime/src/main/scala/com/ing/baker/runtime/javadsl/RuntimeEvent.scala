package com.ing.baker.runtime.javadsl

import java.util

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

case class RuntimeEvent(name: String,
                        providedIngredients: util.Map[String, Value])
  extends common.RuntimeEvent with JavaApi {

  def getProvidedIngredients = providedIngredients

  def getName = name

  def this(name0: String) =
    this(name0, java.util.Collections.emptyMap[String, Value])

  def validate(descriptor: EventDescriptor): util.List[String] =
    asScala.validate(descriptor).asJava

  def asScala: scaladsl.RuntimeEvent =
    scaladsl.RuntimeEvent(name, providedIngredients.asScala.toMap)

  def copy(name0: String): RuntimeEvent = {
    new RuntimeEvent(name0, providedIngredients)
  }

  def copy(providedIngredients0: util.Map[String, Value]): RuntimeEvent = {
    new RuntimeEvent(name, providedIngredients0)
  }
}

object RuntimeEvent {

  def apply(name: String,
            providedIngredients: util.Map[String, Value]): RuntimeEvent =
    new RuntimeEvent(name, providedIngredients)

  def apply(name: String): RuntimeEvent =
    new RuntimeEvent(name, Map[String, Value]().asJava)

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def from(event: Any): RuntimeEvent =
    event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case obj =>
        val scalaEvent = scaladsl.RuntimeEvent.unsafeFrom(event)
        new RuntimeEvent(scalaEvent.name, scalaEvent.providedIngredients.asJava)
    }
}
