package com.ing.baker.recipe.scaladsl

import scala.concurrent.duration.Duration
import scala.collection.immutable.Seq

package object interactions {

  val WaitTime: Ingredient[Duration] =
    Ingredient[Duration]("WaitTime")

  val TimeWaited: Event = Event(name = "TimeWaited")

  val TimerInteraction: Interaction = Interaction(
    name = "TimerInteraction",
    inputIngredients = Seq(
      WaitTime
    ),
    output = Seq(
      TimeWaited
    )
  )
}
