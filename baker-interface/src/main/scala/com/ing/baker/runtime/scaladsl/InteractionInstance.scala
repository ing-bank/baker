package com.ing.baker.runtime.scaladsl

import java.lang.reflect.Method
import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.{Converters, Type}

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, Future}
import scala.reflect.ClassTag
import scala.util.Try

case class InteractionInstance(
    name: String,
    input: Seq[Type],
    run: Seq[IngredientInstance] => Future[Option[EventInstance]],
    output: Option[Map[String, Map[String, Type]]] = None
  ) extends common.InteractionInstance[Future] with ScalaApi { self =>

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override def execute(input: Seq[IngredientInstance]): Future[Option[Event]] =
    run(input)

  def asJava: javadsl.InteractionInstance =
    new javadsl.InteractionInstance {
      override val name: String =
        self.name
      override val input: util.List[Type] =
        self.input.asJava
      override val output: Optional[util.Map[String, util.Map[String, Type]]] =
        self.output match {
          case Some(out) => Optional.of(out.mapValues(_.asJava).asJava)
          case None => Optional.empty[util.Map[String, util.Map[String, Type]]]()
        }
      override def execute(input: util.List[javadsl.IngredientInstance]): CompletableFuture[Optional[javadsl.EventInstance]] =
        FutureConverters
          .toJava(self.run(input.asScala.map(_.asScala)))
          .toCompletableFuture
          .thenApply(_.fold(Optional.empty[javadsl.EventInstance]())(e => Optional.of(e.asJava)))
    }
}

object InteractionInstance {

  def unsafeFromList(implementations: List[AnyRef])(implicit ec: ExecutionContext): List[InteractionInstance] = {
    implementations.map(unsafeFrom(_))
  }

  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionInstance = {
    val method: Method = {
      val unmockedClass = common.unmock(implementation.getClass)
      unmockedClass.getMethods.count(_.getName == "apply") match {
        case 0          => throw new IllegalArgumentException("Implementation does not have a apply function")
        case n if n > 1 => throw new IllegalArgumentException("Implementation has multiple apply functions")
        case _          => unmockedClass.getMethods.find(_.getName == "apply").get
      }
    }
    val name: String = {
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
            clazz => Try {
              clazz.getMethod(method.getName, method.getParameterTypes.toSeq: _*)
            }.isSuccess
          }.getOrElse(method.getDeclaringClass).getSimpleName
      }
    }
    val input: Seq[Type] = {
      method.getGenericParameterTypes.zip(method.getParameters).map { case (typ, _) =>
        try { Converters.readJavaType(typ) }
        catch { case e: Exception =>
          throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
        }
      }
    }
    val run: Seq[IngredientInstance] => Future[Option[EventInstance]] = runtimeInput => {
      // Translate the Value objects to the expected runtimeInput types
      val inputArgs: Seq[AnyRef] = runtimeInput.zip(method.getGenericParameterTypes).map {
        case (value, targetType) => value.value.as(targetType).asInstanceOf[AnyRef]
      }
      val output = method.invoke(implementation, inputArgs: _*)
      val futureClass: ClassTag[Future[Any]] = implicitly[ClassTag[Future[Any]]]
      Option(output) match {
        case Some(event) =>
          event match {
            case runtimeEventAsync if futureClass.runtimeClass.isInstance(runtimeEventAsync) =>
              runtimeEventAsync
                .asInstanceOf[Future[Any]]
                .map(event0 => Some(EventInstance.unsafeFrom(event0)))
            case other =>
              Future.successful(Some(EventInstance.unsafeFrom(other)))
          }
        case None =>
          Future.successful(None)
      }
    }
    InteractionInstance(name, input, run)
  }
}
