package com.ing.baker.test.javadsl

import java.util
import scala.annotation.varargs
import scala.collection.JavaConverters
import scala.reflect.ClassTag;

// TODO try to leave the same method names
case class BakerEventsFlow private(private val events: Set[String]) {

  @varargs def remove(events: String*): BakerEventsFlow =
    new BakerEventsFlow(this.events.diff(events.toSet))

  // TODO just use "remove" method name
  @varargs def removeClass(events: Class[_]*): BakerEventsFlow =
    remove(events.map(_.getSimpleName): _*)

  def remove(events: BakerEventsFlow): BakerEventsFlow =
    remove(events.events.toArray: _*)

  @varargs def add(events: String*): BakerEventsFlow =
    new BakerEventsFlow(this.events ++ events)

  def add(events: BakerEventsFlow): BakerEventsFlow =
    add(events.events.toArray: _*)

  // TODO just use "add" method name
  @varargs def addClass(events: Class[_]*): BakerEventsFlow =
    add(events.map(_.getSimpleName): _*)

  def getEvents: util.Set[String] = JavaConverters.setAsJavaSet(events)
}

object BakerEventsFlow {
  @varargs def of(events: String*): BakerEventsFlow = apply(events.toSet)

  def apply(events: Set[String]): BakerEventsFlow = new BakerEventsFlow(events)

  // TODO just use "of" method name
  @varargs def ofClass(events: Class[_]*): BakerEventsFlow =
    apply(events.map(_.getSimpleName).toSet)
}
