package com.ing.baker.recipe.common

sealed trait InteractionOutput

case class FiresOneOfEvents(events: Event*) extends InteractionOutput