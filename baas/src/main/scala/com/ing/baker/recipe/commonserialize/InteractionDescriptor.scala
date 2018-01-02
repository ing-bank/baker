package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy

case class InteractionDescriptor private(override val name: String,
                                         override val interaction: Interaction,
                                         override val requiredEvents: Set[String] = Set.empty,
                                         override val requiredOneOfEvents: Set[Set[String]] = Set.empty,
                                         override val predefinedIngredients: Map[String, com.ing.baker.types.Value] = Map.empty,
                                         override val overriddenIngredientNames: Map[String, String] = Map.empty,
                                         override val overriddenOutputIngredientName: Option[String] = None,
                                         override val maximumInteractionCount: Option[Int] = None,
                                         override val failureStrategy: Option[InteractionFailureStrategy] = None,
                                         override val eventOutputTransformers: Map[common.Event, common.EventOutputTransformer] = Map.empty)
  extends common.InteractionDescriptor {

  def this(id: common.InteractionDescriptor) =
    this(
      id.name,
      new Interaction(id.interaction),
      id.requiredEvents,
      id.requiredOneOfEvents,
      id.predefinedIngredients,
      id.overriddenIngredientNames,
      id.overriddenOutputIngredientName,
      id.maximumInteractionCount,
      id.failureStrategy,
      id.eventOutputTransformers.map {
        case (event: common.Event, transformer: common.EventOutputTransformer) =>
          new Event(event) -> new EventOutputTransformer(transformer)
      })

  override def equals(obj: scala.Any): Boolean = {
    if (!obj.isInstanceOf[common.InteractionDescriptor])
      return false
    val other: common.InteractionDescriptor = obj.asInstanceOf[common.InteractionDescriptor]
    this.name == other.name &&
      this.interaction == other.interaction &&
      this.maximumInteractionCount == other.maximumInteractionCount &&
      this.requiredEvents == other.requiredEvents &&
      this.requiredOneOfEvents == other.requiredOneOfEvents &&
      this.overriddenIngredientNames == other.overriddenIngredientNames &&
      this.predefinedIngredients == other.predefinedIngredients &&
      this.failureStrategy == other.failureStrategy &&
      this.eventOutputTransformers == other.eventOutputTransformers &&
      this.overriddenOutputIngredientName == other.overriddenOutputIngredientName
  }
}
