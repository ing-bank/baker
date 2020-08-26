package com.ing.bakery.interaction.spring

import com.ing.baker.recipe.javadsl.Interaction

class OutputEvent(outputIngredient: String)

class TestInteraction(append: String) extends Interaction {
  def apply(input: String): OutputEvent = {
    val output = append + ":" + input
    println(output)
    new OutputEvent(output)
  }
}
