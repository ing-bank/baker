package com.ing.baker.test.scaladsl

case class BakerEventsFlow(events: Set[String]) {
  def ::(event: String): BakerEventsFlow = BakerEventsFlow(Set(event) ++ events)

  def ::(event: Class[_]): BakerEventsFlow = event.getSimpleName :: this

  def :::(otherFlow: BakerEventsFlow): BakerEventsFlow = BakerEventsFlow.apply(otherFlow.events ++ events)

  def --(event: String): BakerEventsFlow = BakerEventsFlow(events.filter(e => e != event))

  def --(event: Class[_]): BakerEventsFlow = this -- event.getSimpleName

  def ---(otherFlow: BakerEventsFlow): BakerEventsFlow = BakerEventsFlow(events.diff(otherFlow.events))
}

object EmptyFlow extends BakerEventsFlow(Set.empty)

object BakerEventsFlow {
  def apply(events: String*) = new BakerEventsFlow(events.toSet)
}
