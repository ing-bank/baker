package com.ing.baker.recipe.javadsl

import java.util.UUID

import com.ing.baker.recipe.common
import com.ing.baker.recipe.scaladsl

object JavadslTestHelper {

  //Ingredients
  val initialIngredientCheck: common.Ingredient = scaladsl.Ingredient[String]("initialIngredient")
  val firstProvidedIngredientCheck: common.Ingredient = scaladsl.Ingredient[String]("firstProvidedIngredient")
  val ProcessIdStringCheck: common.Ingredient = scaladsl.Ingredient[String]("$ProcessId$")
  val ProcessIdUUIDCheck: common.Ingredient = scaladsl.Ingredient[UUID]("$ProcessId$")
  //Events
  val interactionProvidedEventCheck: common.Event = scaladsl.Event("InteractionProvidedEvent", Seq.empty)
  val interactionProvidedEvent2Check: common.Event = scaladsl.Event("InteractionProvidedEvent2", Seq.empty)
  val sensoryEventWithIngredientCheck: common.Event = scaladsl.Event("SensoryEventWithIngredient", Seq(initialIngredientCheck))
  val sensoryEventWithoutIngredientCheck: common.Event = scaladsl.Event("SensoryEventWithoutIngredient", Seq.empty)
  //Interactions
  val providesIngredientInteractionCheck: common.Interaction = scaladsl.Interaction("ProvidesIngredientInteraction", Seq(initialIngredientCheck), common.ProvidesIngredient(firstProvidedIngredientCheck))
  val requiresProcessIdStringInteractionCheck: common.Interaction = scaladsl.Interaction("RequiresProcessIdStringInteraction", Seq(ProcessIdStringCheck, initialIngredientCheck), new common.ProvidesNothing)
  val requiresProcessIdUUIDInteractionCheck: common.Interaction = scaladsl.Interaction("RequiresProcessIdUUIDInteraction", Seq(ProcessIdUUIDCheck, initialIngredientCheck), new common.ProvidesNothing)
  val firesEventInteractionCheck: common.Interaction = scaladsl.Interaction("FiresEventInteraction", Seq(initialIngredientCheck), common.FiresOneOfEvents(Seq(interactionProvidedEventCheck)))
  val firesTwoEventInteractionCheck: common.Interaction = scaladsl.Interaction("FiresTwoEventInteraction", Seq(initialIngredientCheck), common.FiresOneOfEvents(Seq(interactionProvidedEventCheck, interactionProvidedEvent2Check)))
}
