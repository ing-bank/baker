package com.ing.baker.runtime.akka.internal

import java.util.UUID
import java.util.concurrent.CompletableFuture

import com.ing.baker.runtime.common.InteractionImplementation
import com.ing.baker.runtime.akka._
import com.ing.baker.runtime.scaladsl.RuntimeEvent
import com.ing.baker.types.{Converters, Type, Value}
import org.slf4j.LoggerFactory

import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, Future}
import scala.reflect.ClassTag
import scala.util.Try

case class MethodInteractionImplementation(implementation: AnyRef)(implicit ec: ExecutionContext) extends InteractionImplementation {

  val log = LoggerFactory.getLogger(classOf[MethodInteractionImplementation])

  val method = {

    val unmockedClass = unmock(implementation.getClass)

    unmockedClass.getMethods.count(_.getName == "apply") match {
      case 0          => throw new IllegalArgumentException("Implementation does not have a apply function")
      case n if n > 1 => throw new IllegalArgumentException("Implementation has multiple apply functions")
      case _          => unmockedClass.getMethods.find(_.getName == "apply").get
    }
  }

  override val name = {

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

  /**
    * The required input.
    */
  override val inputTypes: Seq[Type] = method.getGenericParameterTypes.map { javaType =>
    try {
      Converters.readJavaType(javaType)
    } catch {
      case e: Exception => throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
    }
  }.toSeq

  /**
    * Transforms an object outcome of executing an interaction into a RuntimeEvent if possible.
    */
  private def extractInteractionEventResult(event: Any)(implicit ec: ExecutionContext): Future[RuntimeEvent] = {
    val futureClass: ClassTag[Future[Any]] = implicitly[ClassTag[Future[Any]]]
    val completableFutureClass: ClassTag[CompletableFuture[Any]] = implicitly[ClassTag[CompletableFuture[Any]]]
    event match {
      case runtimeEventAsync if futureClass.runtimeClass.isInstance(runtimeEventAsync) =>
        val typed = runtimeEventAsync.asInstanceOf[Future[Any]]
        typed.map(RuntimeEvent.unsafeFrom)
      case runtimeEventAsync if completableFutureClass.runtimeClass.isInstance(runtimeEventAsync) =>
        val typed = runtimeEventAsync.asInstanceOf[CompletableFuture[Any]]
        FutureConverters.toScala[Any](typed).map(RuntimeEvent.unsafeFrom)
      case other => Future.successful(RuntimeEvent.unsafeFrom(other))
    }
  }

  override def execute(input: Seq[Value]): Future[Option[RuntimeEvent]] =  {

    val invocationId = UUID.randomUUID().toString

    // translate the Value objects to the expected input types
    val inputArgs: Seq[AnyRef] = input.zip(method.getGenericParameterTypes).map {
      case (value, targetType) => value.as(targetType).asInstanceOf[AnyRef]
    }

    if (log.isTraceEnabled)
      log.trace(s"[$invocationId] invoking '$name' with parameters ${inputArgs.toString}")

    // invoke the .apply method
    val output = method.invoke(implementation, inputArgs: _*)

    // if output == null => None, otherwise extract event
    Option(output) match {
      case Some(output0) =>

        if (log.isTraceEnabled)
          log.trace(s"[$invocationId] result: $output0")

        extractInteractionEventResult(output0).map(Option(_))
      case None =>
        Future.successful(None)
    }
  }
}
