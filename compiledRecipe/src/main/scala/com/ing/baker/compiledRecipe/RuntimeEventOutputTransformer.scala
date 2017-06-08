package com.ing.baker.compiledRecipe

trait OutputTransformer {
  def originalEvent: CompiledEvent
  def newEvent: CompiledEvent
  def fn: CompiledEvent => CompiledEvent

  override def equals(obj: scala.Any): Boolean = obj match{
    case other: OutputTransformer =>
      this.originalEvent == other.originalEvent
      this.newEvent == other.newEvent
    case _ => false
  }

  override def toString: String = s"${originalEvent.toString} ⇒ ${originalEvent.toString}"
}

case class RuntimeEventOutputTransformer(originalEvent: CompiledEvent, newEvent: CompiledEvent, fn: CompiledEvent => CompiledEvent) extends OutputTransformer