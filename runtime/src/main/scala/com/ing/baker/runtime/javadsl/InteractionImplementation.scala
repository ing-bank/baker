package com.ing.baker.runtime.javadsl

import java.lang.reflect.Method
import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.akka
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.{Converters, Type, Value}

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.reflect.ClassTag
import scala.util.Try

abstract class InteractionImplementation extends common.InteractionImplementation[CompletableFuture] with JavaApi {

  override type Event = RuntimeEvent

  override type Ingredient = RuntimeIngredient

  override val name: String

  override val input: util.Map[String, Type]

  override val output: Optional[util.Map[String, util.Map[String, Type]]]

  override def execute(input: util.List[RuntimeIngredient]): CompletableFuture[Optional[RuntimeEvent]]

  def asScala: scaladsl.InteractionImplementation =
    scaladsl.InteractionImplementation(
      name,
      input.asScala.toMap,
      if (output.isPresent) Some(output.get.asScala.toMap.mapValues(_.asScala.toMap)) else None,
      input => FutureConverters.toScala(execute(input.map(_.asJava).asJava)
        .thenApply[Option[scaladsl.RuntimeEvent]] {
        optional =>
          if (optional.isPresent) Some(optional.get().asScala)
          else None
      })
    )
}

object InteractionImplementation {

  def from(implementation: AnyRef): InteractionImplementation =
    new InteractionImplementation {

      val method: Method = {
        val unmockedClass = akka.unmock(implementation.getClass)
        unmockedClass.getMethods.count(_.getName == "apply") match {
          case 0          => throw new IllegalArgumentException("Implementation does not have a apply function")
          case n if n > 1 => throw new IllegalArgumentException("Implementation has multiple apply functions")
          case _          => unmockedClass.getMethods.find(_.getName == "apply").get
        }
      }

      override val name: String = {
        Try {
          method.getDeclaringClass.getDeclaredField("name")
        }.toOption match {
          // In case a specific 'name' field was found, this is used
          case Some(field) if field.getType == classOf[String] =>
            field.setAccessible(true)
            field.get(implementation).asInstanceOf[String]
          // Otherwise, try to find the interface that declared the method or falls back to the implementation class
          case None =>
            method.getDeclaringClass.getInterfaces.find {
              clazz => Try { clazz.getMethod(method.getName, method.getParameterTypes.toSeq: _*) }.isSuccess
            }.getOrElse(method.getDeclaringClass).getSimpleName
        }
      }

      override val input: util.Map[String, Type] =
        method.getGenericParameterTypes.zip(method.getParameters).map { case (typ, parameter) =>
          try { parameter.getName -> Converters.readJavaType(typ) }
          catch { case e: Exception =>
            throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
          }
        }.toMap.asJava

      override def execute(runtimeInput: util.List[RuntimeIngredient]): CompletableFuture[Optional[RuntimeEvent]] =  {
        // Translate the Value objects to the expected runtimeInput types
        val inputArgs: Seq[AnyRef] = runtimeInput.asScala.zip(method.getGenericParameterTypes).map {
          case (value, targetType) => value.value.as(targetType).asInstanceOf[AnyRef]
        }
        val output = method.invoke(implementation, inputArgs: _*)
        val futureClass: ClassTag[CompletableFuture[Any]] = implicitly[ClassTag[CompletableFuture[Any]]]
        Option(output) match {
          case Some(event) =>
            event match {
              case runtimeEventAsync if futureClass.runtimeClass.isInstance(runtimeEventAsync) =>
                runtimeEventAsync
                  .asInstanceOf[CompletableFuture[Any]]
                  .thenApply(event0 => Optional.of(RuntimeEvent.from(event0)))
              case other =>
                CompletableFuture
                  .completedFuture(Optional.of(RuntimeEvent.from(other)))
            }
          case None =>
            CompletableFuture.completedFuture(Optional.empty[RuntimeEvent]())
        }
      }

      override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()
    }
}
