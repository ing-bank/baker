package com.ing.baker.il.petrinet

import com.ing.baker.petrinet.api.{Id, Identifiable}

object Transition {

  implicit val identifiable: Identifiable[Transition] = p => Id(p.id)
}

trait Transition {

  def id: Long
  def label: String
}
