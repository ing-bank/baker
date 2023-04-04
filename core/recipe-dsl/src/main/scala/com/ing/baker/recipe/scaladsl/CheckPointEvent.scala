package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common

case class CheckPointEvent private(
                                override val name: String = "",
                                override val requiredEvents: Set[String] = Set.empty,
                                override val requiredOneOfEvents: Set[Set[String]] = Set.empty) extends common.CheckPointEvent {

  def withName(name: String): CheckPointEvent = copy(name = name)

  def withRequiredEvent(event: common.Event): CheckPointEvent =
    copy(requiredEvents = requiredEvents + event.name)

  def withRequiredEvents(events: common.Event*): CheckPointEvent =
    copy(requiredEvents = requiredEvents ++ events.map(_.name))

  def withRequiredOneOfEvents(newRequiredOneOfEvents: common.Event*): CheckPointEvent = {
    if (newRequiredOneOfEvents.nonEmpty && newRequiredOneOfEvents.size < 2)
      throw new IllegalArgumentException("At least 2 events should be provided as 'requiredOneOfEvents'")

    val newRequired: Set[Set[String]] = requiredOneOfEvents + newRequiredOneOfEvents.map(_.name).toSet

    copy(requiredOneOfEvents = newRequired)
  }

}
