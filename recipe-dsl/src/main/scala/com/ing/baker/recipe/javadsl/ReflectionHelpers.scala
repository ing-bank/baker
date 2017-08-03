package com.ing.baker.recipe.javadsl

import java.lang.annotation.Annotation
import java.lang.reflect.Method

import com.ing.baker.recipe.{annotations, common}
import com.thoughtworks.paranamer.AnnotationParanamer

object ReflectionHelpers {

  implicit class MethodReflectionAdditions(method: Method) {
    lazy val paramamer         = new RequiresAnnotationParanamer()
    lazy val getParameterNames = paramamer.lookupParameterNames(method)

    def parameterTypeForName(name: String): Option[Class[_]] =
      getParameterNames.indexWhere(_ == name) match {
        case -1 => None
        case n  => Some(method.getParameterTypes.apply(n))
      }
  }

  class RequiresAnnotationParanamer extends AnnotationParanamer {
    override def getNamedValue(annotation: Annotation): String = {

      val annotationType = annotation.annotationType()

      if (annotationType.equals(classOf[annotations.RequiresIngredient]))
        annotation.asInstanceOf[annotations.RequiresIngredient].value()
      else if (annotationType.equals(classOf[annotations.ProcessId]))
        common.ProcessIdName
      else annotationType.getSimpleName
    }

    override def isNamed(annotation: Annotation): Boolean = true
  }
}
