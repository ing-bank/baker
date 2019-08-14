package com.ing.baker.recipe.javadsl

import java.lang.annotation.Annotation
import java.lang.reflect.{Method, Type}

import com.ing.baker.recipe.{annotations, common}
import com.thoughtworks.paranamer.AnnotationParanamer

object ReflectionHelpers {

  implicit class MethodReflectionAdditions(method: Method) {
    lazy val paramamer         = new RequiresAnnotationParanamer()
    lazy val getParameterNames = paramamer.lookupParameterNames(method)

    def parameterTypeForName(name: String): Option[Type] =
      getParameterNames.indexWhere(_ == name) match {
        case -1 => None
        case n  => Some(method.getGenericParameterTypes.apply(n))
      }
  }

  class RequiresAnnotationParanamer extends AnnotationParanamer {
    override def getNamedValue(annotation: Annotation): String = {

      val annotationType = annotation.annotationType()

      if (annotationType.equals(classOf[annotations.RequiresIngredient]))
        annotation.asInstanceOf[annotations.RequiresIngredient].value()
      else if (annotationType.equals(classOf[javax.inject.Named]))
        annotation.asInstanceOf[javax.inject.Named].value()
      else if (annotationType.equals(classOf[annotations.ProcessId]))
        common.processIdName
      else annotationType.getSimpleName
    }

    override def isNamed(annotation: Annotation): Boolean = true
  }
}
