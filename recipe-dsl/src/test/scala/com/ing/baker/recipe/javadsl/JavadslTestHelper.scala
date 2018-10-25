package com.ing.baker.recipe.javadsl

import java.util.UUID

import com.ing.baker.recipe.common
import com.ing.baker.recipe.scaladsl

object JavadslTestHelper {

  //Ingredients
  val initialIngredientCheck: common.Ingredient = scaladsl.Ingredient[String]("initialIngredient")
  val firstProvidedIngredientCheck: common.Ingredient = scaladsl.Ingredient[String]("firstProvidedIngredient")
  val ProcessIdStringCheck: common.Ingredient = scaladsl.Ingredient[String]("$ProcessId$")
  //Events
  val interactionProvidedEventCheck: common.Event = new scaladsl.Event("InteractionProvidedEvent", Seq.empty, None)
  val interactionProvidedEvent2Check: common.Event = new scaladsl.Event("InteractionProvidedEvent2", Seq.empty, None)
  val sensoryEventWithIngredientCheck: common.Event = new scaladsl.Event("SensoryEventWithIngredient", Seq(initialIngredientCheck), Some(1))
  val sensoryEventWithoutIngredientCheck: common.Event = new scaladsl.Event("SensoryEventWithoutIngredient", Seq.empty, Some(1))

  //Interactions
  val providesIngredientInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("ProvidesIngredientInteraction", Seq(initialIngredientCheck), common.ProvidesIngredient(firstProvidedIngredientCheck))
  val requiresProcessIdStringInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("RequiresProcessIdStringInteraction", Seq(ProcessIdStringCheck, initialIngredientCheck), common.ProvidesNothing)
  val firesEventInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("FiresEventInteraction", Seq(initialIngredientCheck), common.FiresOneOfEvents(interactionProvidedEventCheck))
  val firesTwoEventInteractionCheck: scaladsl.Interaction = scaladsl.Interaction("FiresTwoEventInteraction", Seq(initialIngredientCheck), common.FiresOneOfEvents(interactionProvidedEventCheck, interactionProvidedEvent2Check))
}
