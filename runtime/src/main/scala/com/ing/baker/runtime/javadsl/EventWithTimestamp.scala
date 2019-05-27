package com.ing.baker.runtime.javadsl

class EventWithTimestamp private[javadsl](private val event: RuntimeEvent, private val timestamp: Long) {

  def getEvent: String = event.name

  /**
    * Returns the timestamp associated with this event.
    * Negative timestamps represent an unknown timestamp.
    * Not all `EventList` provide timestamps, for example `BakerResponse.confirmAllEvents`, in this case events will
    * contain negative timestamps.
    *
    * @return A timestamp associated with the event.
    */
  def getTimestamp: Long = timestamp

}
