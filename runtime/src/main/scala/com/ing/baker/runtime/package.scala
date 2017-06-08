package com.ing.baker

import java.lang.reflect.Field

import scala.util.Try

package object runtime {
//  def getNameOrClassName(obj: Any) : String = {
//    Try{
//      obj.getClass.getField("name")
//    }.toOption match {
//      case Some(field) if field.getType == classOf[String]  => field.get(obj).asInstanceOf[String]
//      case _ => obj.getClass.getSimpleName
//    }
//  }

  implicit class FieldWithAdditions(field: Field) {
    def accessAndGet(obj: AnyRef) = {
      field.setAccessible(true)
      field.get(obj)
    }
  }

  def extractIngredientData(obj: Any): Map[String, Any] = {
    val clazz = obj.getClass
    clazz.getDeclaredFields.toSeq.map { field =>
      field.getName -> field.accessAndGet(obj.asInstanceOf[AnyRef])
    }.toMap
  }

  def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]] =
    clazz.getDeclaredFields
      .filterNot(field => field.isSynthetic)
      .map(field => field.getName -> field.getType).toMap
}
