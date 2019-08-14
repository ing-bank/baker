package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.{common, scaladsl}

object JavadslTestHelper {

  //Ingredients
  val initialIngredientCheck: common.Ingredient = scaladsl.Ingredient[String]("initialIngredient")
  val ProcessIdStringCheck: common.Ingredient = scaladsl.Ingredient[String]("$ProcessId$")
  //Events
  val interactionProvidedEventCheck: common.Event = new scaladsl.Event("InteractionProvidedEvent", Seq.empty, None)
  val interactionProvidedEvent2Check: common.Event = new scaladsl.Event("InteractionProvidedEvent2", Seq.empty, None)
  val sensoryEventWithIngredientCheck: common.Event = new scaladsl.Event("SensoryEventWithIngredient", Seq(initialIngredientCheck), Some(1))
  val sensoryEventWithoutIngredientCheck: common.Event = new scaladsl.Event("SensoryEventWithoutIngredient", Seq.empty, Some(1))

  //Interactions
  val requiresProcessIdStringInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("RequiresProcessIdStringInteraction", Seq(ProcessIdStringCheck, initialIngredientCheck), Seq.empty)
  val firesEventInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("FiresEventInteraction", Seq(initialIngredientCheck), Seq((interactionProvidedEventCheck)))
  val firesTwoEventInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("FiresTwoEventInteraction", Seq(initialIngredientCheck), Seq(interactionProvidedEventCheck, interactionProvidedEvent2Check))
}
