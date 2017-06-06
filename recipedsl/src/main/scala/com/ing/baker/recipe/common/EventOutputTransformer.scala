package com.ing.baker.recipe.common

trait OutputTransformer {
  def originalEvent: Event
  def newEvent: Event
  def fn: Event => Event

  override def equals(obj: scala.Any): Boolean = obj match{
    case other: OutputTransformer =>
      this.originalEvent == other.originalEvent
      this.newEvent == other.newEvent
      this.fn(this.originalEvent) == other.fn(this.originalEvent)
    case _ => false
  }

  override def toString: String = s"${originalEvent.toString} ⇒ ${newEvent.toString}"
}

case class EventOutputTransformer(originalEvent: Event, newEvent: Event, fn: Event => Event) extends OutputTransformer
