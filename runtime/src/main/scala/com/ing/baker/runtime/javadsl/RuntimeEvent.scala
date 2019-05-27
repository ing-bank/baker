package com.ing.baker.runtime.javadsl

import java.util

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

class RuntimeEvent(val name: String, val providedIngredients: util.Map[String, Value])
  extends common.RuntimeEvent with JavaApi {

  def this(name0: String) =
    this(name0, java.util.Collections.emptyMap[String, Value])

  def validate(descriptor: EventDescriptor): util.List[String] =
    asScala.validate(descriptor).asJava

  def asScala: scaladsl.RuntimeEvent =
    scaladsl.RuntimeEvent(name, providedIngredients.asScala.toMap)
}

object RuntimeEvent {

  def from(event: Any): RuntimeEvent = {
    val scalaEvent = scaladsl.RuntimeEvent.unsafeFrom(event)
    new RuntimeEvent(scalaEvent.name, scalaEvent.providedIngredients.asJava)
  }
}
