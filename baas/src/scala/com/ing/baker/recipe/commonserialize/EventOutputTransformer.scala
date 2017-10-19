package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common

case class EventOutputTransformer(override val newEventName: String,
                                  override val ingredientRenames: Map[String, String])
  extends common.EventOutputTransformer {

  def this(eventOutputTransformer: common.EventOutputTransformer) =
    this(
      eventOutputTransformer.newEventName,
      eventOutputTransformer.ingredientRenames)
}