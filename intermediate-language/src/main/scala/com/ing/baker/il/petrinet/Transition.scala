package com.ing.baker.il.petrinet

trait Transition[I, O] {
  def id: Long
  def label: String
}
