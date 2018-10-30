package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common

case class Interaction(override val name: String,
                       override val inputIngredients: Seq[Ingredient],
                       override val output: Seq[common.Event])
  extends common.Interaction {

  def this(interaction: common.Interaction) =
    this(
      interaction.name,
      interaction.inputIngredients.map(i => new Ingredient(i)),
      interaction.output)

  override def equals(obj: Any): Boolean = {
    if (!obj.isInstanceOf[common.Interaction])
      return false
    val other: common.Interaction = obj.asInstanceOf[common.Interaction]
    this.name == other.name &&
      this.inputIngredients == other.inputIngredients &&
      this.output == other.output
  }
}
