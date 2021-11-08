package com.ing.baker.test

import scala.annotation.varargs

case class EventsFlow(events: Set[String]) {
  def add(event: String): EventsFlow = EventsFlow(events + event)

  def add(event: Class[_]): EventsFlow = add(event.getSimpleName)

  def add(flow: EventsFlow): EventsFlow = EventsFlow(events ++ flow.events)

  def remove(event: String): EventsFlow = EventsFlow(events.filter(e => e != event))

  def remove(event: Class[_]): EventsFlow = remove(event.getSimpleName)

  def remove(flow: EventsFlow): EventsFlow = EventsFlow(events.diff(flow.events))

  override def toString: String = events.mkString(", ")
}

object EmptyFlow extends EventsFlow(Set.empty)

object EventsFlow {
  def apply(events: String*): EventsFlow = apply(events.toSet)

  @varargs def of(events: String*): EventsFlow = apply(events.toSet)

  @varargs def ofClasses(events: Class[_]*): EventsFlow = apply(events.map(_.getSimpleName).toSet)

  implicit class BakerFlowOps(val flow: EventsFlow) {
    def ::(event: String): EventsFlow = flow.add(event)

    def ::(event: Class[_]): EventsFlow = flow.add(event)

    def :::(other: EventsFlow): EventsFlow = flow.add(other)

    def --(event: String): EventsFlow = flow.remove(event)

    def --(event: Class[_]): EventsFlow = flow.remove(event)

    def ---(other: EventsFlow): EventsFlow = flow.remove(other)
  }
}