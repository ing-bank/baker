package com.ing.baker.runtime.actor.process_instance

import java.io.{PrintWriter, StringWriter}

import cats.data.State
import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.core._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceEventSourcing._
import com.ing.baker.runtime.actor.process_instance.internal.ExceptionStrategy.BlockTransition
import com.ing.baker.runtime.actor.process_instance.internal.{ExceptionStrategy, Instance, Job}
import org.slf4j.LoggerFactory

/**
 * Encapsulates all components required to 'run' a petri net instance
 *
 * @tparam P The place type
 * @tparam T The transition type
 * @tparam S The state type
 * @tparam E The event type
 */
trait ProcessInstanceRuntime[P, T, S, E] {

  val log = LoggerFactory.getLogger("com.ing.baker.runtime.actor.process_instance.ProcessInstanceRuntime")

  /**
    * The event source function for the state associated with a process instance.
    *
    * By default the identity function is used.
    */
  val eventSource: T ⇒ (S ⇒ E ⇒ S) = _ ⇒ (s ⇒ _ ⇒ s)

  /**
    * This function is called when a transition throws an exception.
    *
    * By default the transition is blocked.
    */
  def handleException(job: Job[P, T, S])(throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[P]): ExceptionStrategy = BlockTransition

  /**
    * Returns the task that should be executed for a transition.
    */
  def transitionTask(petriNet: PetriNet[P, T], t: T)(marking: Marking[P], state: S, input: Any): IO[(Marking[P], E)]

  /**
    * Checks if a transition is automatically 'fireable' by the runtime (not triggered by some outside input).
    *
    * By default, cold transitions (without in adjacent places) are not auto fireable.
    */
  def isAutoFireable(instance: Instance[P, T, S], t: T): Boolean = !instance.petriNet.incomingPlaces(t).isEmpty

  /**
    * Defines which tokens from a marking for a particular place are consumable by a transition.
    *
    * By default ALL tokens from that place are consumable.
    *
    * You can override this for example in case you use a colored (data) petri net model with filter rules on the edges.
    */
  def consumableTokens(petriNet: PetriNet[P, T])(marking: Marking[P], p: P, t: T): MultiSet[Any] = marking.getOrElse(p, MultiSet.empty)

  /**
    * Takes a Job specification, executes it and returns a TransitionEvent (asychronously using cats.effect.IO)
    *
    * TODO
    *
    * The use of cats.effect.IO is not really necessary at this point. It was mainly chosen to support cancellation in
    * the future: https://typelevel.org/cats-effect/datatypes/io.html#cancelable-processes
    *
    * However, since that is not used this can be refactored to a simple function: Job -> TransitionEvent
    *
    */
  def jobExecutor(topology: PetriNet[P, T])(implicit transitionIdentifier: Identifiable[T], placeIdentifier: Identifiable[P]): Job[P, T, S] ⇒ IO[TransitionEvent] = {

    def exceptionStackTrace(e: Throwable): String = {
      val sw = new StringWriter()
      e.printStackTrace(new PrintWriter(sw))
      sw.toString
    }

    job ⇒ {

      val startTime = System.currentTimeMillis()
      val transition = job.transition
      val consumed: Marking[Id] = job.consume.marshall

      val jobIO =
        try {
          // calling the transition function could potentially throw an exception
          transitionTask(topology, transition)(job.consume, job.processState, job.input)
        } catch {
          case e: Throwable ⇒ IO.raiseError(e)
        }

      // translates the job output to an EventSourcing.Event
      jobIO.map {
        case (producedMarking, out) ⇒

          val produced: Marking[Id] = producedMarking.marshall

          TransitionFiredEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, produced, out)
      }.handleException {
        // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
        case e: Throwable ⇒
          val failureCount = job.failureCount + 1
          val failureStrategy = handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
          TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), failureStrategy)
      }.handleException {
        // If an exception was thrown while computing the failure strategy we block the interaction from firing
        case e: Throwable =>
          log.error(s"Exception while handling transition failure", e)
          TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), ExceptionStrategy.BlockTransition)
      }
    }
  }

  def enabledParameters(petriNet: PetriNet[P, T])(m: Marking[P]): Map[T, Iterable[Marking[P]]] =
    enabledTransitions(petriNet)(m).view.map(t ⇒ t -> consumableMarkings(petriNet)(m, t)).toMap

  def consumableMarkings(petriNet: PetriNet[P, T])(marking: Marking[P], t: T): Iterable[Marking[P]] = {
    // TODO this is not the most efficient, should break early when consumable tokens < edge weight
    val consumable = petriNet.inMarking(t).map {
      case (place, count) ⇒ (place, count, consumableTokens(petriNet)(marking, place, t))
    }

    // check if any
    if (consumable.exists { case (place, count, tokens) ⇒ tokens.multisetSize < count })
      Seq.empty
    else {
      val consume = consumable.map {
        case (place, count, tokens) ⇒ place -> MultiSet.copyOff[Any](tokens.allElements.take(count))
      }.toMarking

      // TODO lazily compute all permutations instead of only providing the first result
      Seq(consume)
    }
  }

  /**
    * Checks whether a transition is 'enabled' in a marking.
    */
  def isEnabled(petriNet: PetriNet[P, T])(marking: Marking[P], t: T): Boolean = consumableMarkings(petriNet)(marking, t).nonEmpty

  /**
    * Returns all enabled transitions for a marking.
    */
  def enabledTransitions(petriNet: PetriNet[P, T])(marking: Marking[P]): Iterable[T] =
    petriNet.transitions.filter(t ⇒ consumableMarkings(petriNet)(marking, t).nonEmpty)

  /**
    * Creates a job for a specific transition with input, computes the marking it should consume
    */
  def createJob(transition: T, input: Any, correlationId: Option[String] = None): State[Instance[P, T, S], Either[String, Job[P, T, S]]] =
    State { instance ⇒
      instance.isBlockedReason(transition) match {
        case Some(reason) ⇒
          (instance, Left(reason))
        case None ⇒
          enabledParameters(instance.petriNet)(instance.availableMarking).get(transition) match {
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
    * Finds the (optional) first transition that is enabled & automatically fireable
    */
  def firstEnabledJob: State[Instance[P, T, S], Option[Job[P, T, S]]] = State { instance ⇒
    enabledParameters(instance.petriNet)(instance.availableMarking).find {
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
  def allEnabledJobs: State[Instance[P, T, S], Set[Job[P, T, S]]] =
    firstEnabledJob.flatMap {
      case None      ⇒ State.pure(Set.empty)
      case Some(job) ⇒ allEnabledJobs.map(_ + job)
    }
}