package com.ing.baker.il

import java.lang.reflect.{ParameterizedType, Type}

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.il._
import com.ing.baker.petrinet.api.PetriNetAnalysis

import scala.collection.mutable

object RecipeValidations {

  def validateInteraction(compiledRecipe: CompiledRecipe)(interactionTransition: InteractionTransition[_]): Seq[String] = {

    val validationErrors: mutable.MutableList[String] = mutable.MutableList.empty[String]

    if (compiledRecipe.petriNet.inMarking(interactionTransition).isEmpty)
      validationErrors += s"Interaction $interactionTransition does not have any requirements (ingredients or preconditions)! This will result in an infinite execution loop."

    // check if the process id argument type is correct
    interactionTransition.requiredIngredients.toMap.get(processIdName).map {
      case c if c == classOf[String] =>
      case c => validationErrors += s"Non supported process id type: ${c} on interaction: '$interactionTransition'"
    }

    // check if the predefined ingredient is of the expected type
    interactionTransition.predefinedParameters.foreach {
      case (name, value) =>
        interactionTransition.requiredIngredients.toMap.get(name) match {
          case None =>
            validationErrors += s"Predefined argument '$name' is not defined on interaction: '$interactionTransition'"
          case Some(clazz: Class[_]) if !clazz.isInstance(value) =>
            validationErrors += s"Predefined argument '$name' is not of type: ${clazz} on interaction: '$interactionTransition'"
          case Some(pt: ParameterizedType) =>
            getRawClass(pt) match {
              case o if o == classOf[Option[_]] => value match {
                case Some(v) if !getRawClass(pt.getActualTypeArguments.apply(0)).isInstance(v) =>
                  validationErrors += s"Predefined argument '$name' is not of type: ${pt} on interaction: '$interactionTransition'"
                case _ =>
              }
              case o if o == classOf[java.util.Optional[_]] =>
                if (value.isInstanceOf[java.util.Optional[_]]) {
                  val optionalValue = value.asInstanceOf[java.util.Optional[_]]
                  if (optionalValue.isPresent && !getRawClass(pt.getActualTypeArguments.apply(0)).isInstance(optionalValue.get()))
                    validationErrors += s"Predefined argument '$name' is not of type: ${pt} on interaction: '$interactionTransition'"
                }
              case o if !o.isInstance(value) =>
                validationErrors += s"Predefined argument '$name' is not of type: ${pt} on interaction: '$interactionTransition'"
              case o =>
            }
          case _ =>
        }
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
      t.nonProvidedIngredients.flatMap {
        case (name, expectedType) =>
          compiledRecipe.ingredients.get(name) match {
            case None =>
              Some(
                s"Ingredient '$name' for interaction '${t.interactionName}' is not provided by any event or interaction")
            case Some(IngredientType(name, ingredientType)) if !isAssignableFromType(expectedType, ingredientType) =>
              Some(s"Interaction '$t' expects ingredient '$name:$expectedType', however incompatible type: '$ingredientType' was provided")
            case _ =>
              None
          }
      }
    }
  }

  val primitiveTypeMapping: Map[Class[_], Class[_]] = Map(
    java.lang.Boolean.TYPE   -> classOf[java.lang.Boolean],
    java.lang.Byte.TYPE      -> classOf[java.lang.Byte],
    java.lang.Short.TYPE     -> classOf[java.lang.Short],
    java.lang.Character.TYPE -> classOf[java.lang.Character],
    java.lang.Integer.TYPE   -> classOf[java.lang.Integer],
    java.lang.Long.TYPE      -> classOf[java.lang.Long],
    java.lang.Float.TYPE     -> classOf[java.lang.Float],
    java.lang.Double.TYPE    -> classOf[java.lang.Double])

  def validateNonPrimitiveTypedIngredients(compiledRecipe: CompiledRecipe): Seq[String] = {
    compiledRecipe.ingredients.collect {
      case (name, iType) if iType.clazz.isPrimitive =>
        s"Ingredient '$name' is of type '${iType.clazz.getSimpleName}', primitive types are not supported for ingredients, use '${primitiveTypeMapping(iType.clazz).getName}' instead"
    }.toSeq
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
    postCompileValidationErrors ++= validateNonPrimitiveTypedIngredients(compiledRecipe)

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
