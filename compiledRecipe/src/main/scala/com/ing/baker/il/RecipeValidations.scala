package com.ing.baker.il

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import com.ing.baker.il.petrinet.{FiresOneOfEvents, InteractionTransition}

import scala.collection.mutable
import scala.util.Try

object RecipeValidations {

  def validateInteraction(compiledRecipe: CompiledRecipe)(interactionTransition: InteractionTransition[_]): Seq[String] = {

    val validationErrors: mutable.MutableList[String] = mutable.MutableList.empty[String]

    if (compiledRecipe.petriNet.inMarking(interactionTransition).isEmpty)
      validationErrors += s"Interaction $interactionTransition does not have any requirements (ingredients or preconditions)! This will result in an infinite execution loop."

//    val eventClassNotAssignableFromErrors: Seq[String] = interactionTransition match  {
//      case InteractionTransition(providesType: FiresOneOfEvents, _, interactionName: String, _, _, _, _, _) =>
//        providesType.events.flatMap(
//          event =>
//            if (!providesType.outputType.isAssignableFrom(eventClass))
//              Some(s"Event class: $eventClass is not assignable to return type: ${providesType.outputType} for interaction: $interactionName")
//            else None
//        )
//      case _ => Seq.empty
//    }

//    validationErrors ++= eventClassNotAssignableFromErrors

    // check if the process id argument type is correct, TODO remove overlap with code below
    interactionTransition.inputFields.toMap.get(processIdName).map {
      case c if c == classOf[String]         =>
      case c if c == classOf[java.util.UUID] =>
      case c => validationErrors += s"Non supported process id class: ${c.getName} on interaction: '$interactionTransition'"
    }

    // check if the predefined ingredient is of the expected type
    interactionTransition.predefinedParameters.foreach {
      case (name, value) =>
        val parameterTypeOption: Option[Class[_]] = interactionTransition.inputFields.toMap.get(name)
        if(parameterTypeOption.isEmpty)
          validationErrors += s"Predefined argument '$name' is not defined on interaction: '$interactionTransition'"
        else if(!parameterTypeOption.get.isInstance(value))
          validationErrors += s"Predefined argument '$name' is not of type: ${parameterTypeOption.get} on interaction: '$interactionTransition'"
    }
    validationErrors
  }

  def validateInteractions(compiledRecipe: CompiledRecipe): Seq[String] =
    compiledRecipe.interactionTransitions.toSeq.flatMap(validateInteraction(compiledRecipe))

  /**
    * Validates that all required ingredients for interactions are provided for and of the correct type.
    */
  def validateInteractionIngredients(compiledRecipe: CompiledRecipe): Seq[String] = {
    compiledRecipe.interactionTransitions.toSeq.flatMap { t =>
      t.requiredIngredients.flatMap {
        case (name, expectedType) =>
          compiledRecipe.ingredients.get(name) match {
            case None =>
              Some(
                s"Ingredient '$name' for interaction '${t.interactionName}' is not provided by any event or interaction")
            case Some(ingredient) if !expectedType.isAssignableFrom(ingredient.clazz) =>
              Some(
                s"Interaction '$t' expects ingredient '$name:$expectedType', however incompatible type: '$ingredient' was provided")
            case _ =>
              None
          }
      }
    }
  }

  //TODO decide if we really want to check this? Is only of type Event valid for the runtime?
  def validateEventsExtendFromBakerEvent(compiledRecipe: CompiledRecipe): Seq[String] = {
    // check all event classes (sensory events + interaction events)
//    val eventValidationsErrors = compiledRecipe.allEvents.toSeq
//      .filter(c => !classOf[Event].isAssignableFrom(c))
//      .map(c => s"Event class: $c does not extend from com.ing.baker.api.Event")
//
//    // check all interactions that provide an ingredient (instead of an event)
////    val interactionIngredientsValidationsErrors = compiledRecipe.interactionTransitions.toSeq
////      .filter(_.providesIngredient)
////      .map(_.method.getReturnType)
////      .filter(c => !classOf[java.io.Serializable].isAssignableFrom(c))
////      .map(c => s"Ingredient class: $c does not extend from java.io.Serializable")
////    eventValidationsErrors ++ interactionIngredientsValidationsErrors
//    eventValidationsErrors
    Seq.empty
  }

  def validateNoCycles(compiledRecipe: CompiledRecipe): Seq[String] =
    compiledRecipe.petriNet.innerGraph.findCycle
      .map(c => s"The petri net topology contains a cycle: $c")
      .toSeq

  /**
    * Validates the compiled recipe.
    *
    * The validations are:
    *   1. Validate that an implementation is provided for the interaction
    *   2. Validate that the return type the interaction matches the expectations from the annotation
    *   3. Check if all the required events are provided
    *   4. Check if all ingredients are provided
    *   5. Check if the provided ingredients are of the same type as the expected ingredients
    */
  def postCompileValidations(compiledRecipe: CompiledRecipe,
                             validationSettings: ValidationSettings): CompiledRecipe = {

    // TODO don't use a mutable list but instead a more functional solutions such as folding or a writer monad
    val postCompileValidationErrors = mutable.MutableList.empty[String]

    postCompileValidationErrors ++= validateInteractionIngredients(compiledRecipe)
    postCompileValidationErrors ++= validateInteractions(compiledRecipe)
    postCompileValidationErrors ++= validateEventsExtendFromBakerEvent(compiledRecipe)

    if (!validationSettings.allowCycles)
    postCompileValidationErrors ++= validateNoCycles(compiledRecipe)

    if (!validationSettings.allowDisconnectedness && !compiledRecipe.petriNet.innerGraph.isConnected)
    postCompileValidationErrors += "The petri net topology is not completely connected"

    compiledRecipe.copy(
      validationErrors = compiledRecipe.validationErrors ++ postCompileValidationErrors)
  }

  @throws[NonSerializableException]
  def assertEventsAndIngredientsAreSerializable(compiledRecipe: CompiledRecipe)(implicit actorSystem: ActorSystem): Unit = {
    val serialization = SerializationExtension(actorSystem)

    val hasAkkaSerializer = (clazz: Class[_]) => Try { serialization.serializerFor(clazz) }.isSuccess

    val ingredientSerializationErrors: Seq[String] =
      compiledRecipe.ingredients.mapValues(_.clazz)
        .filterNot{case (c, v) => hasAkkaSerializer(v) }
        .map{case (c, v) => s"Ingredient $c of $v is not serializable by akka"}.toSeq

    val allErrors: Seq[String] = ingredientSerializationErrors

    if (allErrors.nonEmpty) throw new NonSerializableException(allErrors.mkString(", "))
  }
}
