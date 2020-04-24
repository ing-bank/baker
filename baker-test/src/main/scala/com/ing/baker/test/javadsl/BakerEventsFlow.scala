package com.ing.baker.test.javadsl

import java.util

import scala.annotation.varargs
import scala.collection.JavaConverters;

// TODO try to leave the same method names
case class BakerEventsFlow private(private val events: Set[String]) {

  @varargs def remove(events: String*): BakerEventsFlow =
    new BakerEventsFlow(this.events.diff(events.toSet))

  @varargs def removeClass(events: Class[_]*): BakerEventsFlow =
    remove(events.map(_.getSimpleName): _*)

  @varargs def add(events: String*): BakerEventsFlow =
    new BakerEventsFlow(this.events ++ events)

  @varargs def addClass(events: Class[_]*): BakerEventsFlow =
    add(events.map(_.getSimpleName): _*)

  def getEvents: util.Set[String] = JavaConverters.setAsJavaSet(events)
}

object BakerEventsFlow {
  @varargs def of(events: String*): BakerEventsFlow = apply(events.toSet)

  def apply(events: Set[String]): BakerEventsFlow = new BakerEventsFlow(events)

  @varargs def ofClass(events: Class[_]*): BakerEventsFlow =
    apply(events.map(_.getSimpleName).toSet)
}
