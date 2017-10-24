package com.ing.baker.recipe.commonserialize

import com.ing.baker.recipe.common

case class EventOutputTransformer(override val newEventName: String,
                                  override val ingredientRenames: Map[String, String])
  extends common.EventOutputTransformer {

  def this(eventOutputTransformer: common.EventOutputTransformer) =
    this(
      eventOutputTransformer.newEventName,
      eventOutputTransformer.ingredientRenames)

  override def equals(obj: Any): Boolean = {
    if (!obj.isInstanceOf[common.EventOutputTransformer])
      return false
    val other: common.EventOutputTransformer = obj.asInstanceOf[common.EventOutputTransformer]
    this.newEventName == other.newEventName &&
      this.ingredientRenames == other.ingredientRenames
  }
}