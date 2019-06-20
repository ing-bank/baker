package com.ing.baker.runtime.javadsl

import java.util

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

case class RuntimeEvent(name: String,
                        providedIngredients: util.Map[String, Value],
                        occurredOn: Long)
  extends common.RuntimeEvent with JavaApi {

  def getProvidedIngredients = providedIngredients

  def getName = name

  def getOccurredOn: Long = occurredOn

  def this(name0: String) =
    this(name0, java.util.Collections.emptyMap[String, Value], System.currentTimeMillis())

  def validate(descriptor: EventDescriptor): util.List[String] =
    asScala.validate(descriptor).asJava

  def asScala: scaladsl.RuntimeEvent =
    scaladsl.RuntimeEvent(name, providedIngredients.asScala.toMap, occurredOn)

  def copy(name0: String): RuntimeEvent = {
    new RuntimeEvent(name0, providedIngredients, occurredOn)
  }

  def copy(providedIngredients0: util.Map[String, Value]): RuntimeEvent = {
    new RuntimeEvent(name, providedIngredients0, occurredOn)
  }

  def copy(occurredOn0: Long): RuntimeEvent = {
    new RuntimeEvent(name, providedIngredients, occurredOn0)
  }
}

object RuntimeEvent {

  def apply(name: String,
            providedIngredients: util.Map[String, Value]): RuntimeEvent =
    new RuntimeEvent(name, providedIngredients, System.currentTimeMillis())

  def apply(name: String): RuntimeEvent =
    new RuntimeEvent(name, Map[String, Value]().asJava, System.currentTimeMillis())

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def from(event: Any): RuntimeEvent =
    from(event, System.currentTimeMillis())

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def from(event: Any, occurredOn: Long): RuntimeEvent =
    event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case obj =>
        val scalaEvent = scaladsl.RuntimeEvent.unsafeFrom(event)
        new RuntimeEvent(scalaEvent.name, scalaEvent.providedIngredients.asJava, System.currentTimeMillis())
    }
}
