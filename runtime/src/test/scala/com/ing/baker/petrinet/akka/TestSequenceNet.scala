package com.ing.baker.petrinet.akka

import com.ing.baker.petrinet.dsl.colored.SequenceNet

sealed trait Event
case class Added(n: Int) extends Event
case class Removed(n: Int) extends Event

trait TestSequenceNet extends SequenceNet[Set[Int], Event] {

  override val eventSourceFunction: Set[Int] ⇒ Event ⇒ Set[Int] = set ⇒ {
    case Added(c)   ⇒ set + c
    case Removed(c) ⇒ set - c
  }
}
