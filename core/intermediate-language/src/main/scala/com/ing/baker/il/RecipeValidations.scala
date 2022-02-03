package com.ing.baker.il

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.petrinet.api._
import com.ing.baker.types

object RecipeValidations {

  def validateInteraction(compiledRecipe: CompiledRecipe)(interactionTransition: InteractionTransition): Seq[String] = {
    val interactionWithNoRequirementsValidation : Seq[String] =
      Some(s"Interaction $interactionTransition does not have any requirements (ingredients or preconditions)! This will result in an infinite execution loop.")
        .filter(_ => compiledRecipe.petriNet.inMarking(interactionTransition).isEmpty).toSeq

    // check if the process id argument type is correct
    val processIdArgumentTypeValidation : Seq[String] =
        interactionTransition.requiredIngredients.filter(id => id.name.equals(recipeInstanceIdName)).flatMap {
          case IngredientDescriptor(_, types.CharArray) => None
          case IngredientDescriptor(_, incompatibleType) => Some(s"Non supported process id type: ${incompatibleType} on interaction: '${interactionTransition.interactionName}'")
        }

    // check if the predefined ingredient is of the expected type
    val predefinedIngredientOfExpectedTypeValidation : Iterable[String] =
      interactionTransition.predefinedParameters.flatMap {
        case (name, value) =>
          interactionTransition.requiredIngredients.find(_.name == name) match {
            case None =>
              Some(s"Predefined argument '$name' is not defined on interaction: '${interactionTransition.interactionName}'")
            case Some(ingredientDescriptor) if !value.isInstanceOf(ingredientDescriptor.`type`) =>
              Some(s"Predefined argument '$name' is not of type: ${ingredientDescriptor.`type`} on interaction: '${interactionTransition.interactionName}'")
            case _ =>
              None
          }
      }

    interactionWithNoRequirementsValidation ++ processIdArgumentTypeValidation ++ predefinedIngredientOfExpectedTypeValidation
  }

  def validateInteractions(compiledRecipe: CompiledRecipe): Seq[String] = {
    compiledRecipe.interactionTransitions.toSeq.flatMap(validateInteraction(compiledRecipe))
  }


  /**
    * Validates that all required ingredients for interactions are provided for and of the correct type.
    */
  def validateInteractionIngredients(compiledRecipe: CompiledRecipe): Seq[String] = {
    compiledRecipe.interactionTransitions.toSeq.flatMap { t =>
      t.nonProvidedIngredients.flatMap {
        case (IngredientDescriptor(name, expectedType)) =>
          compiledRecipe.allIngredients.find(_.name == name) match {
            case None =>
              Some(
                s"Ingredient '$name' for interaction '${t.interactionName}' is not provided by any event or interaction")
            case Some(IngredientDescriptor(name, ingredientType)) if !expectedType.isAssignableFrom(ingredientType) =>
              Some(s"Interaction '${t.interactionName}' expects ingredient '$name:$expectedType', however incompatible type: '$ingredientType' was provided")
            case _ =>
              None
          }
      }
    }
  }

  def validateNoCycles(compiledRecipe: CompiledRecipe): Seq[String] = {
    val cycle: Option[compiledRecipe.petriNet.innerGraph.Cycle] = compiledRecipe.petriNet.innerGraph.findCycle
    cycle.map(c => s"The petrinet topology contains a cycle: $c").toList
  }

  def validateAllInteractionsExecutable(compiledRecipe: CompiledRecipe): Seq[String] = {
    val rootNode = PetriNetAnalysis.calculateCoverabilityTree(compiledRecipe.petriNet, compiledRecipe.initialMarking.multiplicities)

    compiledRecipe.interactionTransitions filterNot { interaction =>
      rootNode.isCoverable(compiledRecipe.petriNet.inMarking(interaction))
    } map (interaction => s"${interaction.interactionName} is not executable") toSeq

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

    val postCompileValidationErrors : Seq[String] = Seq(
      validateInteractionIngredients(compiledRecipe),
      validateInteractions(compiledRecipe),
      if (!validationSettings.allowCycles) validateNoCycles(compiledRecipe) else Seq(),
      if (!validationSettings.allowDisconnectedness && !compiledRecipe.petriNet.innerGraph.isConnected) Seq("The petrinet topology is not completely connected") else Seq(),
      if (!validationSettings.allowNonExecutableInteractions) validateAllInteractionsExecutable(compiledRecipe) else Seq(),
    ).flatten

    compiledRecipe.copy(
      validationErrors = compiledRecipe.validationErrors ++ postCompileValidationErrors)
  }
}

