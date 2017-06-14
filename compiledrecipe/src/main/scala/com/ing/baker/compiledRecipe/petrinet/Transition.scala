package com.ing.baker.compiledRecipe.petrinet

trait Transition[I, O] {
  def id: Long
  def label: String
}
