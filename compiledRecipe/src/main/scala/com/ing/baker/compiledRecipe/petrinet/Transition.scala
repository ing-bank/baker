package com.ing.baker.compiledRecipe.petrinet

trait Transition[I, O, S] {
  def id: Long
  def label: String
}
