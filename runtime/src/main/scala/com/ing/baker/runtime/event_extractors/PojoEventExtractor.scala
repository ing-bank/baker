package com.ing.baker.runtime.event_extractors

import java.lang.reflect.Field

import com.ing.baker.runtime.core.RuntimeEvent

class PojoEventExtractor extends EventExtractor {
  implicit class FieldWithAdditions(field: Field) {
    def accessAndGet(obj: AnyRef) = {
      field.setAccessible(true)
      field.get(obj)
    }
  }

  override def extractEvent(obj: Any): RuntimeEvent = {
    val clazz = obj.getClass
    val ingredients: Seq[(String, AnyRef)] = clazz.getDeclaredFields.toSeq
      .filter(field => !field.isSynthetic())
      .map (field => field.getName -> field.accessAndGet(obj.asInstanceOf[AnyRef]))
    RuntimeEvent(clazz.getSimpleName, ingredients)
  }
}