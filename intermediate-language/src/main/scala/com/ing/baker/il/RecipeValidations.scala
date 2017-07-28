package com.ing.baker.il

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.petrinet.api.PetriNetAnalysis

import scala.collection.mutable

object RecipeValidations {

  def validateInteraction(compiledRecipe: CompiledRecipe)(interactionTransition: InteractionTransition[_]): Seq[String] = {

    val validationErrors: mutable.MutableList[String] = mutable.MutableList.empty[String]

    if (compiledRecipe.petriNet.inMarking(interactionTransition).isEmpty)
      validationErrors += s"Interaction $interactionTransition does not have any requirements (ingredients or preconditions)! This will result in an infinite execution loop."

    // check if the process id argument type is correct, TODO remove overlap with code below
    interactionTransition.inputFields.toMap.get(processIdName).map {
      case c if c == classOf[String] =>
      case c if c == classOf[java.util.UUID] =>
      case c => validationErrors += s"Non supported process id class: ${c.getName} on interaction: '$interactionTransition'"
    }

    // check if the predefined ingredient is of the expected type
    interactionTransition.predefinedParameters.foreach {
      case (name, value) =>
        val parameterTypeOption: Option[Class[_]] = interactionTransition.inputFields.toMap.get(name)
        if (parameterTypeOption.isEmpty)
          validationErrors += s"Predefined argument '$name' is not defined on interaction: '$interactionTransition'"
        else if (!parameterTypeOption.get.isInstance(value))
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

  def validateNoCycles(compiledRecipe: CompiledRecipe): Seq[String] = {
    val cycle = compiledRecipe.petriNet.innerGraph.findCycle
    cycle map (c => s"The petrinet topology contains a cycle: $c") toSeq
  }

  def validateAllInteractionsExecutable(compiledRecipe: CompiledRecipe): Seq[String] = {
    val rootNode = PetriNetAnalysis.calculateCoverabilityTree(compiledRecipe.petriNet, compiledRecipe.initialMarking.multiplicities)

    compiledRecipe.interactionTransitions filterNot { interaction =>
      rootNode.isCoverable(compiledRecipe.petriNet.inMarking(interaction))
    } map (interaction => s"$interaction is not executable") toSeq

  }

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

    if (!validationSettings.allowCycles)
      postCompileValidationErrors ++= validateNoCycles(compiledRecipe)

    if (!validationSettings.allowDisconnectedness && !compiledRecipe.petriNet.innerGraph.isConnected)
      postCompileValidationErrors += "The petrinet topology is not completely connected"

    if (!validationSettings.allowNonExecutableInteractions)
      postCompileValidationErrors ++= validateAllInteractionsExecutable(compiledRecipe)

    compiledRecipe.copy(
      validationErrors = compiledRecipe.validationErrors ++ postCompileValidationErrors)
  }

}
