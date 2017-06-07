package com.ing.baker.compiledRecipe

abstract class EventImpl {
  def name(): String = this.getClass.getSimpleName
}
