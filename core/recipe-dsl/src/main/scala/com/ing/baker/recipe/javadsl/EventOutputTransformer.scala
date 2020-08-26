package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common

case class EventOutputTransformer(override val newEventName: String,
                                  override val ingredientRenames: Map[String, String]) extends common.EventOutputTransformer