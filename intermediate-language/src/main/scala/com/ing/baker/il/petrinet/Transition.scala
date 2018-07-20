package com.ing.baker.il.petrinet

import com.ing.baker.petrinet.api.{Id, Identifiable}

object Transition {

  implicit val identifiable: Identifiable[Transition[_]] = p => Id(p.id)
}

trait Transition[I] {

  def id: Long
  def label: String
}
