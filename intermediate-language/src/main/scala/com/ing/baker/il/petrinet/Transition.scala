package com.ing.baker.il.petrinet

trait Transition[I] {
  def id: Long
  def label: String
}
