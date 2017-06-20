package com.ing.baker.recipe.javadsl

import java.lang.annotation.Annotation
import java.lang.reflect.{Field, Method, ParameterizedType}

import com.ing.baker.recipe.{annotations, common}
import com.thoughtworks.paranamer.AnnotationParanamer

import scala.concurrent.Future

object ReflectionHelpers {

  implicit class MethodReflectionAdditions(method: Method) {
    lazy val paramamer         = new RequiresAnnotationParanamer()
    lazy val getParameterNames = paramamer.lookupParameterNames(method)

    def isAsynchronous       = returnsScalaFuture() || returnsJavaFuture()
    def returnsScalaFuture() = method.getReturnType.equals(classOf[Future[_]])
    def returnsJavaFuture()  = method.getReturnType.equals(classOf[java.util.concurrent.Future[_]])

    def getFirstTypeParameter =
      method.getGenericReturnType
        .asInstanceOf[ParameterizedType]
        .getActualTypeArguments
        .apply(0)
        .asInstanceOf[Class[_]]

    def isVoid                = method.getReturnType.equals(classOf[Void])

    def parameterTypeForName(name: String): Option[Class[_]] =
      getParameterNames.indexWhere(_ == name) match {
        case -1 => None
        case n  => Some(method.getParameterTypes.apply(n))
      }

    def processIdClass: Option[Class[_]] = parameterTypeForName(common.ProcessIdName)
  }

  implicit class FieldWithAdditions(field: Field) {
    def accessAndGet(obj: AnyRef) = {
      field.setAccessible(true)
      field.get(obj)
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
