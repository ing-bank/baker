package com.ing.baker.petrinet.runtime

import cats.data.State

/**
 * Given a token game picks the next job(s) to be executed
 */
class JobPicker[P[_], T](tokenGame: TokenGame[P, T]) {

  /**
   * Fires a specific transition with input, computes the marking it should consume
   */
  def createJob[S, I](transition: T, input: I, correlationId: Option[String] = None): State[Instance[P, T, S], Either[String, Job[P, T, S]]] =
    State { instance ⇒
      instance.isBlockedReason(transition) match {
        case Some(reason) ⇒
          (instance, Left(reason))
        case None ⇒
          tokenGame.enabledParameters(instance.process)(instance.availableMarking).get(transition) match {
            case None ⇒
              (instance, Left(s"Not enough consumable tokens"))
            case Some(params) ⇒
              val job = Job[P, T, S](instance.nextJobId(), correlationId, instance.state, transition, params.head, input)
              val updatedInstance = instance.copy[P, T, S](jobs = instance.jobs + (job.id -> job))
              (updatedInstance, Right(job))
          }
      }
    }

  /**
   * Checks if a transition is automatically fireable by the runtime (not triggered by some outside input)
   *
   * By default, cold transitions (without in adjacent places) are not picked.
   */
  def isAutoFireable[S](instance: Instance[P, T, S], t: T) = !instance.process.incomingPlaces(t).isEmpty

  /**
   * Finds the (optional) first transition that is enabled & automatically fireable
   */
  def firstEnabledJob[S]: State[Instance[P, T, S], Option[Job[P, T, S]]] = State { instance ⇒
    tokenGame.enabledParameters(instance.process)(instance.availableMarking).find {
      case (t, markings) ⇒ !instance.isBlockedReason(t).isDefined && isAutoFireable(instance, t)
    }.map {
      case (t, markings) ⇒
        val job = Job[P, T, S](instance.nextJobId(), None, instance.state, t, markings.head, null)
        (instance.copy[P, T, S](jobs = instance.jobs + (job.id -> job)), Some(job))
    }.getOrElse((instance, None))
  }

  /**
   * Finds all automated enabled transitions.
   */
  def allEnabledJobs[S]: State[Instance[P, T, S], Set[Job[P, T, S]]] =
    firstEnabledJob[S].flatMap {
      case None      ⇒ State.pure(Set.empty)
      case Some(job) ⇒ allEnabledJobs[S].map(_ + job)
    }
}
