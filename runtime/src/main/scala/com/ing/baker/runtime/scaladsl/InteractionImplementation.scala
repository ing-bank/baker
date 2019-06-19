package com.ing.baker.runtime.scaladsl

import java.lang.reflect.Method
import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.akka
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.types.{Converters, Type, Value}

import scala.concurrent.{ExecutionContext, Future}
import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.reflect.ClassTag
import scala.util.Try

case class InteractionImplementation(
    name: String,
    input: Map[String, Type],
    output: Option[Map[String, Map[String, Type]]],
    run: Map[String, Value] => Future[Option[RuntimeEvent]]
  ) extends common.InteractionImplementation[Future] with ScalaApi { self =>

  override type Event = RuntimeEvent

  override def execute(input: Map[String, Value]): Future[Option[Event]] =
    run(input)

  def asJava: javadsl.InteractionImplementation =
    new javadsl.InteractionImplementation {
      override val name: String =
        self.name
      override val input: util.Map[String, Type] =
        self.input.asJava
      override val output: Optional[util.Map[String, util.Map[String, Type]]] =
        self.output match {
          case Some(out) => Optional.of(out.mapValues(_.asJava).asJava)
          case None => Optional.empty[util.Map[String, util.Map[String, Type]]]()
        }
      override def execute(input: util.Map[String, Value]): CompletableFuture[Optional[javadsl.RuntimeEvent]] =
        FutureConverters
          .toJava(self.run(input.asScala.toMap))
          .toCompletableFuture
          .thenApply(_.fold(Optional.empty[javadsl.RuntimeEvent]())(e => Optional.of(e.asJava)))
    }
}

object InteractionImplementation {

  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionImplementation = {
    val method: Method = {
      val unmockedClass = akka.unmock(implementation.getClass)
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
    val input: Map[String, Type] = {
      method.getGenericParameterTypes.zip(method.getParameters).map { case (typ, parameter) =>
        try { parameter.getName -> Converters.readJavaType(typ) }
        catch { case e: Exception =>
          throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
        }
      }.toMap
    }
    val run: Map[String, Value] => Future[Option[RuntimeEvent]] = input => {
      // Translate the Value objects to the expected input types
      val inputArgs: Seq[AnyRef] = method.getParameters.map { p =>
        input(p.getName).as(p.getParameterizedType).asInstanceOf[AnyRef]
      }.toSeq
      val output = method.invoke(implementation, inputArgs: _*)
      val futureClass: ClassTag[Future[Any]] = implicitly[ClassTag[Future[Any]]]
      Option(output) match {
        case Some(event) =>
          event match {
            case runtimeEventAsync if futureClass.runtimeClass.isInstance(runtimeEventAsync) =>
              runtimeEventAsync
                .asInstanceOf[Future[Any]]
                .map(event0 => Some(RuntimeEvent.unsafeFrom(event0)))
            case other =>
              Future.successful(Some(RuntimeEvent.unsafeFrom(other)))
          }
        case None =>
          Future.successful(None)
      }
    }
    InteractionImplementation(name, input, None, run)
  }
}
