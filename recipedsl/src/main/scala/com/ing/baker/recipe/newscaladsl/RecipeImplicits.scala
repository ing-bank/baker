package com.ing.baker.recipe.newscaladsl

import com.ing.baker.recipe.common.InteractionFailureStrategy.BlockInteraction
import com.ing.baker.recipe.common.{Interaction, InteractionDescriptor, _}
import com.ing.baker.recipe.newscaladsl.RecipeImplicits._
import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, InteractionDescriptorImpl}

import scala.reflect.ClassTag


object newRecipe {

  implicit class newRecipe(recipeOps: RecipeOps) extends Recipe {
    /**
      * The name of the recipe.
      */
    override def name: String = recipeOps.name


    implicit def seqOfToSeqInteractionDescriptor[T](ofs: Seq[of[_]]) : Seq[InteractionDescriptor[_]] =
      ofs.map(ofToInteractionDescriptor(_))

    def ofToInteractionDescriptor[T](of: of[T]): InteractionDescriptor[T] =
      InteractionDescriptorImpl(implicitly[ClassTag[T]].runtimeClass.asInstanceOf[Class[T]], requiredEvents = of.requiredEvents)

    /**
      * The set of interactions.
      */
    override def interactionDescriptors: Seq[InteractionDescriptor[_]] = recipeOps.interactionTypes

    /**
      * The set of sieves.
      */
    override def sieveDescriptors: Seq[InteractionDescriptor[_]] = Seq.empty

    /**
      * The set of events.
      */
    override def events: Set[Class[_ <: Event]] = recipeOps.events

    /**
      * The default interaction failure strategy.
      */
    override def defaultFailureStrategy: InteractionFailureStrategy = BlockInteraction
  }
}

object RecipeImplicits {

  case class of[T <: Interaction: ClassTag](requiredEvents: Set[Class[_ <: Event]] = Set.empty) {
    def withRequiredEvent[C <: Event : ClassTag]: of[T] =
      copy(requiredEvents = requiredEvents + implicitly[ClassTag[C]].runtimeClass.asInstanceOf[Class[C]])
  }

  implicit def stringToRecipeOps(name: String): RecipeOps = new RecipeOps(name, Seq.empty, Set.empty)
  implicit class EventClassWrapper[E <: Event](val event: E)

  class RecipeOps(val name: String, val interactionTypes: Seq[of[_ <: Interaction]], val events: Set[Class[_ <: Event]]) {
    def withInteractions(newInteractionType: of[_ <: Interaction]*): RecipeOps = {
      new RecipeOps(name, interactionTypes ++ newInteractionType, events)
    }
    def withEvents(newEvents: EventClassWrapper[_ <: Event]*): RecipeOps = {
      new RecipeOps(name, interactionTypes, events ++ newEvents.map(_.event.getClass))
    }
  }
}
