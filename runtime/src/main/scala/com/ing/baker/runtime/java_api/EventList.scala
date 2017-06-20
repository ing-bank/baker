package com.ing.baker.runtime.java_api

import com.ing.baker.runtime.core.RuntimeEvent

import scala.collection.JavaConverters._

object EventList {
  def CreateFromStringList(events: java.util.List[String]): EventList =
    new EventList(events.asScala.map(RuntimeEvent(_, Map.empty)))

  def CreateFromObjectList(events: java.util.List[Object]): EventList =
    new EventList(events.asScala.map(obj => RuntimeEvent(obj.getClass.getSimpleName, Map.empty)))
}

/**
  * Java API class wrapping a sequence of events for a process instance.
  *
  * @param events The event sequence.
  */
class EventList(private val events: Seq[RuntimeEvent]) extends java.util.AbstractList[AnyRef] {

  def this() = this(Seq.empty)

  def this(events: java.util.List[RuntimeEvent]) = this(events.asScala)

  override def get(index: Int): AnyRef = events.apply(index).asInstanceOf[AnyRef]

  override def size(): Int = events.size

  /**
    * Returns whether an event occurred or not.
    *
    * @param clazz The event class.
    *
    * @return
    */
  def hasEventOccurred(clazz: Class[_]): Boolean = events.exists(e => e.name equals clazz.getSimpleName)

  /**
    * Returns the number of times an event occurred.
    *
    * @param clazz The event class.
    *
    * @return The number of times an event occurred.
    */
  def getEventCount(clazz: Class[_]): Int = events.count(e => e.name equals clazz.getSimpleName)

  /**
    * Returns a list of simple names of all events that have fired.
    *
    * @return A list of event classes.
    */
  def getEventNameList: java.util.List[String] = events.map(_.name).asJava
}
