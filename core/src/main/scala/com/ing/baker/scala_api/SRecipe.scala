package com.ing.baker.scala_api

import com.ing.baker.api.Event
import com.ing.baker.compiler.{CompiledRecipe, Recipe, RecipeCompiler}
import com.ing.baker.core.{InteractionDescriptor, InteractionFailureStrategy}

case class SRecipe(override val name: String,
                   override val interactionDescriptors: Seq[InteractionDescriptor[_]],
                   override val sieveDescriptors: Seq[InteractionDescriptor[_]],
                   override val events: Set[Class[_<: Event]],
                   override val defaultFailureStrategy: InteractionFailureStrategy =
                        InteractionFailureStrategy.BlockInteraction)
    extends Recipe {

  def withInteractions(newInteractions: InteractionDescriptor[_]*): SRecipe =
    copy(interactionDescriptors = newInteractions)

  def withEvents(eventClasses: Class[_<: Event]*): SRecipe = copy(events = eventClasses.toSet)

  def withDefaultFailureStrategy(newDefaultFailureStrategy: InteractionFailureStrategy) =
    copy(defaultFailureStrategy = newDefaultFailureStrategy)

  def compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(this)
}

object SRecipe {
  def apply(name: String) : SRecipe = SRecipe(name, Seq.empty, Seq.empty, Set.empty)

  def apply(name: String, interactions: Seq[InteractionDescriptor[_]], events: Set[Class[_<: Event]]) : SRecipe =
    SRecipe(name, interactions, Seq.empty, events)
}
