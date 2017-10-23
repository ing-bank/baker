package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionOutput

case class Interaction(override val name: String,
                       override val inputIngredients: Seq[Ingredient],
                       override val output: InteractionOutput)
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
