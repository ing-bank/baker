package com.ing.baker.recipe.common

/**
  * A Recipe combines a set of interactions & events.
  */
trait Recipe {

  /**
    * The name of the recipe.
    */
  def name: String

  /**
    * The set of interactions.
    */
  def interactionDescriptors: Seq[InteractionDescriptor[_]]

  /**
    * The set of sieves.
    */
  def sieveDescriptors: Seq[InteractionDescriptor[_]]

  /**
    * The set of events.
    */
  def events: Set[Class[_ <: Event]]

  /**
    * The default interaction failure strategy.
    */
  def defaultFailureStrategy: InteractionFailureStrategy
}
