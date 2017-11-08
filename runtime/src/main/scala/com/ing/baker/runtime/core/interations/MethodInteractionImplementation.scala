package com.ing.baker.runtime.core.interations

import java.lang.reflect.{Method, ParameterizedType, Type}
import java.util.UUID

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.types.{Converters, IngredientDescriptor, Value}
import com.ing.baker.runtime.core.Baker.eventExtractor
import com.ing.baker.runtime.core.{BakerException, RuntimeEvent}
import com.ing.baker.runtime.petrinet.FatalInteractionException
import org.slf4j.{Logger, LoggerFactory}
import MethodInteractionImplementation._
import com.ing.baker.il.EventType

import scala.util.Try

object MethodInteractionImplementation {

  val log = LoggerFactory.getLogger(classOf[MethodInteractionImplementation])

  /**
    * This method looks for any valid name that this interaction implements
    * This is its own class name
    * The class name of any interface it implements
    * The value of the field "name"
    *
    * @param obj
    * @return List of possible interaction names this obj can be implementing
    */
  def getPossibleInteractionNamesForImplementation(obj: Any): Set[String] = {
    val nameField: String = Try {
      obj.getClass.getDeclaredField("name")
    }.toOption match {
      case Some(field) if field.getType == classOf[String] => {
        field.setAccessible(true)
        field.get(obj).asInstanceOf[String]
      }
      case None => ""
    }
    val interfaceNames: Seq[String] = obj.getClass.getInterfaces.map(_.getSimpleName).toSeq
    Set[String](obj.getClass.getSimpleName, nameField).filterNot(s => s equals "") ++ interfaceNames
  }


  def anyRefToInteractionImplementations(any: AnyRef): Seq[InteractionImplementation] = {
    any.getClass.getMethods.count(m => m.getName == "apply") match {
      case 0 => throw new BakerException("Method does not have a apply function")
      case n if n > 1 => throw new BakerException("Method has multiple apply functions")
      case _ => ()
    }

    val applyMethod: Method = any.getClass.getMethods.find(m => m.getName == "apply").get
    getPossibleInteractionNamesForImplementation(any).map { name =>
      // TODO give the actual event types, not Set.empty

      new MethodInteractionImplementation(name, any, applyMethod.getParameterTypes.toSeq, Set.empty)
    }.toSeq

  }

  def applyMethod(clazz: Class[_]): Method = {
    val method = clazz.getMethods.find(_.getName == "apply").get
    val className = method.getDeclaringClass.getName

    if (className.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = className.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      val orginalClass = clazz.getClassLoader.loadClass(originalName)
      applyMethod(orginalClass)
    }
    else
      method
  }

  def createRuntimeEvent[I](interaction: InteractionTransition[I], output: Any): RuntimeEvent = {

    // when the interaction does not fire an event, Void or Unit is a valid output type
    if (interaction.eventsToFire.isEmpty && output == null)
      RuntimeEvent(interaction.interactionName, Seq.empty)

    // if the interaction directly produces an ingredient
    else if (interaction.providedIngredientEvent.isDefined) {
      val eventToComplyTo = interaction.providedIngredientEvent.get
      eventForProvidedIngredient(interaction.interactionName, eventToComplyTo.name, output, eventToComplyTo.ingredientTypes.head)
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

      if (interaction.originalEvents.exists(runtimeEvent.isInstanceOfEventType))
        runtimeEvent

      else {
        val msg: String = s"Output: $output fired by interaction ${interaction.interactionName} but could not link it to any known event for the interaction"
        log.error(msg)
        throw new FatalInteractionException(msg)
      }
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
                                           override val requiredIngredients: Seq[Type],
                                           override val returnType: Set[EventType]) extends InteractionImplementation {

  val log: Logger = LoggerFactory.getLogger(MethodInteractionImplementation.getClass)

  val method = MethodInteractionImplementation.applyMethod(implementation.getClass())

  override def isValidForInteraction(interaction: InteractionTransition[_]): Boolean =

    interaction.originalInteractionName == name

  override def execute(interaction: InteractionTransition[_], input: Seq[Value]): RuntimeEvent =  {

    val invocationId = UUID.randomUUID().toString

    val inputArgs = input.zip(method.getGenericParameterTypes).map {
      case (value, targetType) =>

        value.toJava(targetType)
    }

    log.trace(s"[$invocationId] invoking '$name' with parameters ${inputArgs.toString}")
    val output = method.invoke(implementation, inputArgs.asInstanceOf[Seq[AnyRef]]: _*)
    log.trace(s"[$invocationId] result: $output")

    val event = createRuntimeEvent(interaction, output)

    event
  }
}
