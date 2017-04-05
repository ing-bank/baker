package com.ing.baker.scala_api

import com.ing.baker.compiler.{CompiledRecipe, Recipe, RecipeCompiler}
import com.ing.baker.core.{InteractionDescriptor, InteractionFailureStrategy}

import scala.reflect.ClassTag

case class RecipeImpl(override val name: String,
                      override val interactionDescriptors: Seq[InteractionDescriptor[_]],
                      override val sieveDescriptors: Seq[InteractionDescriptor[_]],
                      override val events: Set[Class[_]],
                      override val defaultFailureStrategy: InteractionFailureStrategy =
                        InteractionFailureStrategy.BlockInteraction)
    extends Recipe {

  def withProjection[T: ClassTag, Y: ClassTag](ingredientName: String): (String, Y) = ???

  def withInteractions(newInteractions: InteractionDescriptor[_]*): RecipeImpl =
    copy(interactionDescriptors = newInteractions)

  def withEvents(eventClasses: Class[_]*): RecipeImpl = copy(events = eventClasses.toSet)

  def withDefaultFailureStrategy(newDefaultFailureStrategy: InteractionFailureStrategy) =
    copy(defaultFailureStrategy = newDefaultFailureStrategy)

  def compileRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(this)
}

object Recipe {
  def apply(name: String) = RecipeImpl(name, Seq.empty, Seq.empty, Set.empty)

  def apply(name: String, interactions: Seq[InteractionDescriptor[_]], events: Set[Class[_]]) =
    RecipeImpl(name, interactions, Seq.empty, events)
}
