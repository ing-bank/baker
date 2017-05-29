//package com.ing.baker.runtime.core
//
//import akka.actor.ActorSystem
//import akka.util.Timeout
//import cats.Monoid
//import cats.data.State
//import com.ing.baker.compiledRecipe.CompiledRecipe
//import com.ing.baker.compiledRecipe.transitions.InteractionTransition
//import com.ing.baker.core.ProcessState
//import fs2.Strategy
//import io.kagera.akka.actor.AkkaObjectSerializer
//import io.kagera.api._
//import io.kagera.execution.EventSourcing._
//import io.kagera.execution._
//import io.kagera.persistence.Serialization
//
//import scala.concurrent.duration._
//import scala.language.postfixOps
//import scala.reflect.ClassTag
//
//object EventRecovery {
//
//  val defaultTimeout: Timeout = Timeout(60 seconds)
//
//  implicit class FoldStateFn[T](i: Iterable[T]) {
//    def mapCombine[S, Out: Monoid](fn: T => State[S, Out]): State[S, Out] =
//      i.map(fn).reduce[State[S, Out]] {
//        case (a, b) => a.flatMap(aOut => b.map(bOut => implicitly[Monoid[Out]].combine(aOut, bOut)))
//      }
//  }
//
//  sealed trait Event
//
//  case class SensoryEventFired[R](result: R) extends Event
//
//  case class InteractionCompleted[T: ClassTag](result: Any) extends Event {
//    def interactionClass = implicitly[ClassTag[T]].runtimeClass
//  }
//
//  def interaction[T: ClassTag](result: Any): InteractionCompleted[T] = InteractionCompleted(result)
//
//  def event[R](result: R): SensoryEventFired[R] = SensoryEventFired(result)
//
//  def serializeEvents(compiledRecipe: CompiledRecipe, events: List[EventSourcing.Event])(implicit actorSystem: ActorSystem): List[AnyRef] = {
//
//    val serializer = new Serialization[Place, Transition, ProcessState](new AkkaObjectSerializer(actorSystem))
//    var instance: Instance[Place, Transition, ProcessState] = Instance.uninitialized[Place, Transition, ProcessState](compiledRecipe.petriNet)
//    val eventSourceFn = (t: Transition[_,_,_]) ⇒ t.updateState.asInstanceOf[(ProcessState ⇒ Any ⇒ ProcessState)]
//
//    // do a functional fold map like thing here
//    events.map { e =>
//      val serializedEvent = serializer.serializeEvent(e)(instance)
//      instance = EventSourcing.apply[Place, Transition, ProcessState, _](eventSourceFn)(instance)(e)
//      serializedEvent
//    }
//  }
//
//  def transformToKageraEvents(id: java.util.UUID, history: List[Event], compiledRecipe: CompiledRecipe): List[EventSourcing.Event] = {
//
//    val petriNet = compiledRecipe.petriNet
//
//    def transitionForSensoryEvent(clazz: Class[_]): Transition[_, _, _] =
//      petriNet.transitions.getById(clazz.getName.hashCode.toLong)
//
//    def transitionForInteraction(clazz: Class[_]): InteractionTransition[_] =
//      petriNet.transitions.getById(clazz.getSimpleName.hashCode.toLong).asInstanceOf[InteractionTransition[_]]
//
//    val executor = new JobPicker[Place, Transition](new Colored)(Strategy.sequential)
//
//    val step: State[Instance[ProcessState], List[TransitionEvent]] = newEnabledJobs[ProcessState]
//      .map(_.filterNot(_.transition.isInteraction))
//      .flatMap(applyJobs(executor))
//
//    val applyEvent: TransitionFiredEvent => State[Instance[Place, Transition, ProcessState], Unit] =
//      e => State.modify { instance ⇒ EventSourcing.apply[ProcessState](instance)(e) }
//
//    val updateAndStep: TransitionFiredEvent => State[Instance[Place, Transition, ProcessState], List[TransitionEvent[Transition]]] =
//      e => applyEvent(e).flatMap(_ => step.map(e :: _))
//
//    import cats.instances.list._
//
//    val stateHistory = history.mapCombine[Instance[Place, Transition, ProcessState], List[TransitionEvent[Transition]]] {
//
//      case SensoryEventFired(e) => State.inspect { instance: Instance[ProcessState] =>
//
//        val transition = transitionForSensoryEvent(e.getClass)
//        val time = System.currentTimeMillis()
//        val consumed: Marking[Place] = Marking.empty[Place]
//        val produced: Marking[Place] = petriNet.outMarking(transition).toMarking
//
//        TransitionFiredEvent(instance.nextJobId(), transition, time, time, consumed, produced, Some(e))
//
//      }.flatMap(updateAndStep)
//
//      case e@InteractionCompleted(output) => State.inspect { instance: Instance[ProcessState] =>
//
//        val transition = transitionForInteraction(e.interactionClass)
//        val time = System.currentTimeMillis()
//        val consumed: Marking[Place] = petriNet.inMarking(transition).toMarking
//        val produced: Marking[Place] = transition.createProducedMarking(petriNet.outMarking(transition))(output.asInstanceOf[AnyRef])
//
//        TransitionFiredEvent(instance.nextJobId(), transition, time, time, consumed, produced, Some(output))
//
//      }.flatMap(updateAndStep)
//    }
//
//    val initialState: Instance[Place, Transition, ProcessState] =
//      Instance[Place, Transition, ProcessState](petriNet, 1, compiledRecipe.initialMarking, ProcessState(id, Map.empty), Map.empty)
//
//    val initializedEvent = InitializedEvent(compiledRecipe.initialMarking, ProcessState(id, Map.empty))
//
//    val transitionEvents = stateHistory.runA(initialState).value
//
//    initializedEvent :: transitionEvents
//  }
//}
