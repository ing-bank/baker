package com.ing.baker.runtime.java_api

import com.ing.baker.runtime.core.RuntimeEvent

import scala.collection.JavaConverters._

object EventList {

  /**
    * Constructor from raw string events with unknown timestamps represented with negative time.
    *
    * @param events Simple events represented by strings.
    *
    * @return A new EventList.
    */
  def CreateFromStringList(events: java.util.List[String]): EventList =
    new EventList(events.asScala.map(RuntimeEvent(_, Seq.empty) -> -1l))

  /**
    * Constructor from java object events with unknown timestamps represented with negative time.
    *
    * @param events Simple events represented by strings.
    *
    * @return A new EventList.
    */
  def CreateFromObjectList(events: java.util.List[Object]): EventList =
    new EventList(events.asScala.map(obj => RuntimeEvent(obj.getClass.getSimpleName, Seq.empty) -> -1l))

  /**
    * Constructor from scala `Seq` of `RuntimeEvent` with unknown timestamps represented with negative time.
    *
    * @param events events to be added.
    *
    * @return A new EventList.
    */
  def ScalaWithNoTimestamps(events: Seq[RuntimeEvent]): EventList =
    new EventList(events.map(_ -> -1l))

}

/**
  * Java API class wrapping a sequence of events for a process instance.
  *
  * @param events The event sequence.
  */
class EventList(private val eventsWithTimestamp: Seq[(RuntimeEvent, Long)]) extends java.util.AbstractList[AnyRef] {

  def this() = this(Seq.empty)

  def this(events: java.util.List[RuntimeEvent]) = this(events.asScala.map(_ -> -1l))

  private val events: Seq[RuntimeEvent] = eventsWithTimestamp.map(_._1)

  override def get(index: Int): AnyRef = events.apply(index).asInstanceOf[AnyRef]

  override def size(): Int = events.size

  /**
    * Returns whether an event occurred or not.
    *
    * @param clazz The event class.
    *
    * @return
    */
  def hasEventOccurred(clazz: Class[_]): Boolean =
    events.exists(e => e.name equals clazz.getSimpleName)

  /**
    * Returns the number of times an event occurred.
    *
    * @param clazz The event class.
    *
    * @return The number of times an event occurred.
    */
  def getEventCount(clazz: Class[_]): Int =
    events.count(e => e.name equals clazz.getSimpleName)

  /**
    * Returns a list of simple names of all events that have fired.
    *
    * @return A list of event classes.
    */
  def getEventNameList: java.util.List[String] = events.map(_.name).asJava

  /**
    * Returns a list of simple names of all events that have fired together with their timestamps.
    * Negative timestamps represent an unknown timestamp.
    * Not all `EventList` provide timestamps, for example `BakerResponse.confirmAllEvents`, in this case events will
    * contain negative timestamps.
    *
    * @return A list of events together with a timestamp.
    */
  def getEventNameListWithTimestamp: java.util.List[EventWithTimestamp] =
    eventsWithTimestamp.map { case (event, timestamp) => new EventWithTimestamp(event, timestamp) }.asJava
}
