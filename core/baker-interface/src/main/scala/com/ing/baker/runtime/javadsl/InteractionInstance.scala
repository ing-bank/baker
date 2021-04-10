package com.ing.baker.runtime.javadsl

import cats.effect.IO
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.{Converters, Type}

import java.lang.reflect.Method
import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.reflect.ClassTag
import scala.util.Try

abstract class InteractionInstance extends common.InteractionInstance[CompletableFuture] with JavaApi {

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override val name: String

  override val input: util.List[Type]

  override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()

  override def execute(input: util.List[IngredientInstance]): CompletableFuture[Optional[EventInstance]]

  private def wrapExecuteToFuture(input: Seq[scaladsl.IngredientInstance]) = {
    FutureConverters.toScala(execute(input.map(_.asJava).asJava)
      .thenApply[Option[scaladsl.EventInstance]] {
        optional =>
          if (optional.isPresent) Some(optional.get().asScala)
          else None
      })
  }

  private def outputOrNone = {
    if (output.isPresent) Some(output.get.asScala.toMap.mapValues(_.asScala.toMap)) else None
  }

  def asScala: scaladsl.InteractionInstance = {
    scaladsl.InteractionInstance(
      name,
      input.asScala,
      input => wrapExecuteToFuture(input),
      outputOrNone
    )
  }

  def asEffectful: InteractionInstanceF[IO] = {
    InteractionInstanceF.build(
      name,
      input.asScala,
      input => IO.fromFuture(IO(wrapExecuteToFuture(input)))(cs),
      outputOrNone
    )
  }

}

object InteractionInstance {

  def fromList(implementations: java.util.List[AnyRef]): java.util.List[InteractionInstance] = {
    implementations.asScala.map(from).asJava
  }

  def from(implementation: AnyRef): InteractionInstance =
    new InteractionInstance {

      val method: Method = {
        val unmockedClass = common.unmock(implementation.getClass)
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

      override val input: util.List[Type] =
        method.getGenericParameterTypes.zip(method.getParameters).map { case (typ, _) =>
          try { Converters.readJavaType(typ) }
          catch { case e: Exception =>
            throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
          }
        }.toSeq.asJava

      override def execute(runtimeInput: util.List[IngredientInstance]): CompletableFuture[Optional[EventInstance]] =  {
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
                  .thenApply(event0 => Optional.of(EventInstance.from(event0)))
              case other =>
                CompletableFuture
                  .completedFuture(Optional.of(EventInstance.from(other)))
            }
          case None =>
            CompletableFuture.completedFuture(Optional.empty[EventInstance]())
        }
      }

      override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()
    }
}
