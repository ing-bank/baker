package com.ing.baker

import java.security.MessageDigest

import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, MissingEventTransition, MultiFacilitatorTransition, Place, Transition}


package object il {

  val processIdName = "$ProcessID$"
  val SuccessEventAppend = "Successful"
  val exhaustedEventAppend = "RetryExhausted"

  implicit class TransitionAdditions(transition: Transition) {

    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case _: InteractionTransition => true
    }

    def isMultiFacilitatorTransition: Boolean = transition.isInstanceOf[MultiFacilitatorTransition]

    def isEventMissing: Boolean = transition.isInstanceOf[MissingEventTransition]

    def isSensoryEvent: Boolean =
      transition match {
      case EventTransition(_, true, _) => true
      case _ => false
    }
  }

  def sha256HashCode(str: String): Long = {
    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    BigInt(1, sha256Digest.digest(str.getBytes("UTF-8"))).toLong
  }
}
