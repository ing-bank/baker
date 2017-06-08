package com.ing.baker

import scala.util.Try

package object runtime {
  def getNameOrClassName(obj: Any) : String = {
    Try{
      obj.getClass.getField("name")
    }.toOption match {
      case Some(field) if field.getType == classOf[String]  => field.get(obj).asInstanceOf[String]
      case _ => obj.getClass.getSimpleName
    }
  }
}
