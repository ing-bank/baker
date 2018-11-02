package com.ing.baker.petrinet.runtime

import java.io.{PrintWriter, StringWriter}

import cats.data.State
import cats.effect.IO
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.EventSourcing.{TransitionEvent, TransitionFailedEvent, TransitionFiredEvent}
import com.ing.baker.petrinet.runtime.ExceptionStrategy.BlockTransition
import org.slf4j.LoggerFactory

/**
 * Encapsulates all components required to 'run' a petri net instance
 *
 * @tparam P The place type
 * @tparam T The transition type
 * @tparam S The state type
 * @tparam E The event type
 */
trait PetriNetRuntime[P, T, S, E] {

  val log = LoggerFactory.getLogger("com.ing.baker.petrinet.runtime.PetriNetRuntime")

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
  def isAutoFireable[S](instance: Instance[P, T, S], t: T): Boolean = !instance.process.incomingPlaces(t).isEmpty

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
  def jobExecutor(topology: PetriNet[P, T]): Job[P, T, S] ⇒ IO[TransitionEvent[T]] = {

    def exceptionStackTrace(e: Throwable): String = {
      val sw = new StringWriter()
      e.printStackTrace(new PrintWriter(sw))
      sw.toString
    }

    job ⇒ {

      val startTime = System.currentTimeMillis()
      val transition = job.transition

      val jobIO =
        try {
          // calling the transition function could potentially throw an exception
          transitionTask(topology, transition)(job.consume, job.processState, job.input)
        } catch {
          case e: Throwable ⇒ IO.raiseError(e)
        }

      // translates the job output to an EventSourcing.Event
      jobIO.map {
        case (produced, out) ⇒
          TransitionFiredEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, produced, out)
      }.handleException {
        // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
        case e: Throwable ⇒
          val failureCount = job.failureCount + 1
          val failureStrategy = handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
          TransitionFailedEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, job.input, exceptionStackTrace(e), failureStrategy)
      }.handleException {
        // If an exception was thrown while computing the failure strategy we block the interaction from firing
        case e: Throwable =>
          log.error(s"Exception while handling transition failure", e)
          TransitionFailedEvent(job.id, transition, job.correlationId, startTime, System.currentTimeMillis(), job.consume, job.input, exceptionStackTrace(e), ExceptionStrategy.BlockTransition)
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
    * Fires a specific transition with input, computes the marking it should consume
    */
  def createJob[S, I](transition: T, input: I, correlationId: Option[String] = None): State[Instance[P, T, S], Either[String, Job[P, T, S]]] =
    State { instance ⇒
      instance.isBlockedReason(transition) match {
        case Some(reason) ⇒
          (instance, Left(reason))
        case None ⇒
          enabledParameters(instance.process)(instance.availableMarking).get(transition) match {
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
  def firstEnabledJob[S]: State[Instance[P, T, S], Option[Job[P, T, S]]] = State { instance ⇒
    enabledParameters(instance.process)(instance.availableMarking).find {
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