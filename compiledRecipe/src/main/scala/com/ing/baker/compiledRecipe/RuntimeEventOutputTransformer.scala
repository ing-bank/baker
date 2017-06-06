package com.ing.baker.compiledRecipe

trait OutputTransformer {
  def originalEvent: RuntimeEvent
  def newEvent: RuntimeEvent
  def fn: RuntimeEvent => RuntimeEvent

  override def equals(obj: scala.Any): Boolean = obj match{
    case other: OutputTransformer =>
      this.originalEvent == other.originalEvent
      this.newEvent == other.newEvent
    case _ => false
  }

  override def toString: String = s"${originalEvent.toString} ⇒ ${originalEvent.toString}"
}

case class RuntimeEventOutputTransformer(originalEvent: RuntimeEvent, newEvent: RuntimeEvent, fn: RuntimeEvent => RuntimeEvent) extends OutputTransformer