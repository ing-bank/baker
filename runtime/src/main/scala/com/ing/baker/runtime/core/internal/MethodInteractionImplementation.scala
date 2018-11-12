package com.ing.baker.runtime.core.internal

import java.lang.reflect.Method
import java.util.UUID

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.core._
import com.ing.baker.runtime.core.internal.MethodInteractionImplementation._
import com.ing.baker.runtime.core.{BakerException, RuntimeEvent}
import com.ing.baker.types.{Converters, Type, Value}
import org.slf4j.{Logger, LoggerFactory}

import scala.collection.JavaConverters._
import scala.util.Try

object MethodInteractionImplementation {

  val log = LoggerFactory.getLogger(classOf[MethodInteractionImplementation])

  def getInteractionName(impl: Any, method: Method): String = {

    Try {
      method.getDeclaringClass.getDeclaredField("name")
    }.toOption match {
      case Some(field) if field.getType == classOf[String] =>
        field.setAccessible(true)
        field.get(impl).asInstanceOf[String]
      case None =>
        method.getDeclaringClass.getInterfaces.find {
          clazz => Try { clazz.getMethod(method.getName, method.getParameterTypes.toSeq: _*) }.isSuccess
        }.getOrElse(method.getDeclaringClass).getSimpleName
    }
  }

  def getApplyMethod(clazz: Class[_]): Method = {

    val unmockedClass = unmock(clazz)

    unmockedClass.getMethods.count(_.getName == "apply") match {
      case 0          => throw new BakerException("Method does not have a apply function")
      case n if n > 1 => throw new BakerException("Method has multiple apply functions")
      case _          => unmockedClass.getMethods.find(_.getName == "apply").get
    }
  }
}

case class MethodInteractionImplementation(implementation: AnyRef) extends InteractionImplementation {

  val method = getApplyMethod(implementation.getClass)

  override val name = getInteractionName(implementation, method)

  val log: Logger = LoggerFactory.getLogger(MethodInteractionImplementation.getClass)

  /**
    * The required input.
    */
  override val inputTypes: Seq[Type] = method.getGenericParameterTypes.map {
    jType => try { Converters.readJavaType(jType) } catch {
      case e: Exception => throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
    }
  }.toSeq

  override def execute(input: Seq[Value]): Option[RuntimeEvent] =  {

    val invocationId = UUID.randomUUID().toString

    val inputArgs = input.zip(method.getGenericParameterTypes).map {
      case (value, targetType) => value.as(targetType)
    }

    if (log.isTraceEnabled)
      log.trace(s"[$invocationId] invoking '$name' with parameters ${inputArgs.toString}")

    val output = method.invoke(implementation, inputArgs.asInstanceOf[Seq[AnyRef]]: _*)

    if (log.isTraceEnabled)
      log.trace(s"[$invocationId] result: $output")

    // when the interaction does not fire an event, Void or Unit is a valid output type
    if (output == null)
      None
    else {
      val runtimeEvent: RuntimeEvent = Baker.extractEvent(output)

      Some(runtimeEvent)
    }
  }
}
