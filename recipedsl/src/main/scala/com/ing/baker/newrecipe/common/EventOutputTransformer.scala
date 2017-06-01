package com.ing.baker.newrecipe.common

trait OutputTransformer {
  def originalEvent: Event
  def newEvent: Event
  def fn: Event => Event

  override def equals(obj: scala.Any): Boolean = obj match{
    case other: OutputTransformer =>
      this.originalEvent == other.originalEvent
      this.newEvent == other.newEvent
      this.fn == other.fn
    case _ => false
  }

  override def toString: String = s"${originalEvent.toString} ⇒ ${originalEvent.toString}"
}