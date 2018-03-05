package com.ing.baker.runtime.core.interations

import java.lang.reflect.Method
import java.util.UUID

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.runtime.core.Baker.eventExtractor
import com.ing.baker.runtime.core.interations.MethodInteractionImplementation._
import com.ing.baker.runtime.core.{BakerException, RuntimeEvent}
import com.ing.baker.runtime.petrinet.FatalInteractionException
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

    clazz.getMethods.count(_.getName == "apply") match {
      case 0          => throw new BakerException("Method does not have a apply function")
      case n if n > 1 => throw new BakerException("Method has multiple apply functions")
      case _ => ()
    }

    val method = clazz.getMethods.find(_.getName == "apply").get

    val className = method.getDeclaringClass.getName

    if (className.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = className.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      val orginalClass = clazz.getClassLoader.loadClass(originalName)
      getApplyMethod(orginalClass)
    }
    else
      method
  }

  def anyRefToInteractionImplementations(impl: AnyRef): Seq[InteractionImplementation] = {

    val applyMethod: Method = getApplyMethod(impl.getClass)

    val interactionNames = Set(getInteractionName(impl, getApplyMethod(impl.getClass)))

    interactionNames.map { name => new MethodInteractionImplementation(name, impl, applyMethod, Set.empty)}.toSeq
  }

  def toImplementationMap(implementations: java.lang.Iterable[AnyRef]): Map[String, InteractionImplementation] =
    toImplementationMap(implementations.asScala)

  def toImplementationMap(implementations: Iterable[AnyRef]): Map[String, InteractionImplementation] =
    implementations.flatMap(anyRefToInteractionImplementations _).map {
      i => i.name -> i
    }.toMap

  def createRuntimeEvent[I](interaction: InteractionTransition[I], output: Any): Option[RuntimeEvent] = {

    // when the interaction does not fire an event, Void or Unit is a valid output type
    if (interaction.eventsToFire.isEmpty && output == null)
      None

    // if the interaction directly produces an ingredient
    else if (interaction.providedIngredientEvent.isDefined) {
      val eventToComplyTo = interaction.providedIngredientEvent.get
      Some(eventForProvidedIngredient(interaction.interactionName, eventToComplyTo.name, output, eventToComplyTo.ingredients.head))
    }
    else {
      val runtimeEvent = eventExtractor.extractEvent(output)

      val nullIngredientNames = runtimeEvent.providedIngredients.collect {
        case (name, null) => name
      }

      if(nullIngredientNames.nonEmpty) {
        val msg: String = s"Interaction ${interaction.interactionName} returned null value for ingredients: ${nullIngredientNames.mkString(",")}"
        log.error(msg)
        throw new FatalInteractionException(msg)
      }

      interaction.originalEvents.find(_.name == runtimeEvent.name) match {
        case None =>
          throw new FatalInteractionException(s"No event with name '${runtimeEvent.name}' is known by this interaction")
        case Some(eventType) =>
          val errors = runtimeEvent.validateEvent(eventType)

          if (errors.nonEmpty)
            throw new FatalInteractionException(s"Event '${runtimeEvent.name}' does not match the expected type: ${errors.mkString}")
      }

      Some(runtimeEvent)
    }
  }

  def eventForProvidedIngredient[I](interactionName: String, runtimeEventName: String, providedIngredient: Any, ingredientToComplyTo: IngredientDescriptor): RuntimeEvent = {

    if (providedIngredient == null) {
      val msg: String = s"null value provided for ingredient '${ingredientToComplyTo.name}' for interaction '${interactionName}'"
      log.error(msg)
      throw new FatalInteractionException(msg)
    }

    val ingredientValue = Converters.toValue(providedIngredient)

    if (ingredientValue.isInstanceOf(ingredientToComplyTo.`type`))
      RuntimeEvent(runtimeEventName , Seq((ingredientToComplyTo.name, ingredientValue)))
    else {
      throw new FatalInteractionException(
        s"""
           |Ingredient: ${ingredientToComplyTo.name} provided by an interaction but does not comply to the expected type
           |Expected  : ${ingredientToComplyTo.`type`}
           |Provided  : $providedIngredient
         """.stripMargin)
    }
  }
}

case class MethodInteractionImplementation(override val name: String,
                                           implementation: AnyRef,
                                           method: Method,
                                           returnType: Set[EventDescriptor]) extends InteractionImplementation {

  val log: Logger = LoggerFactory.getLogger(MethodInteractionImplementation.getClass)

  /**
    * The required input.
    */
  override val inputTypes: Seq[Type] = method.getGenericParameterTypes.map {
    jType => try { Converters.readJavaType(jType) } catch {
      case e: Exception => throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
    }
  }.toSeq

  override def execute(interaction: InteractionTransition[_], input: Seq[Value]): Option[RuntimeEvent] =  {

    val invocationId = UUID.randomUUID().toString

    val inputArgs = input.zip(method.getGenericParameterTypes).map {
      case (value, targetType) => value.as(targetType)
    }

    log.trace(s"[$invocationId] invoking '$name' with parameters ${inputArgs.toString}")
    val output = method.invoke(implementation, inputArgs.asInstanceOf[Seq[AnyRef]]: _*)
    log.trace(s"[$invocationId] result: $output")

    createRuntimeEvent(interaction, output)
  }

}
