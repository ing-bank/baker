package com.ing.baker.newrecipe.common

trait OutputTransformer {
  def originalEvent: Event
  def newEvent: Event
  def fn: Event => Event

  override def toString: String = s"${originalEvent.toString} ⇒ ${originalEvent.toString}"
}