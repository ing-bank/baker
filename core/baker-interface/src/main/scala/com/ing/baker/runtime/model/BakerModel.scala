package com.ing.baker.runtime.model

import cats.implicits._
import cats.data.{State, StateT}
import cats.effect.IO
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.petrinet.{Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.{Marking, PetriNet}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.common.BakerException.{IllegalEventException, NoSuchProcessException, NoSuchRecipeException, ProcessAlreadyExistsException}
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment, InteractionInstance, RecipeInformation, SensoryEventResult}
import com.ing.baker.types.Value
import com.ing.baker.runtime.model.BakerModel._
import com.ing.baker.runtime.model.PetriNettyJuice.{TransitionFiring, TransitionState}
import com.ing.baker.petrinet.api._

import scala.util.Random

trait Baker[F[_]] {

  def addRecipe(compiledRecipe: CompiledRecipe): F[String]

  def getRecipe(recipeId: String): F[RecipeInformation]

  def getAllRecipes: F[Map[String, RecipeInformation]]

  def addInteractionInstance(implementation: InteractionInstance): F[Unit]

  def bake(recipeId: String, recipeInstanceId: String): F[Unit]

  def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): F[SensoryEventResult]
}

object PetriNettyJuice {

  sealed trait FailureStrategy

  object FailureStrategy {
    case object BlockTransition extends FailureStrategy
    case class RetryWithDelay(delay: Long) extends FailureStrategy {
      require(delay >= 0, "Delay must be greater then zero")
    }
    case class Continue[O](marking: Marking[Place], output: O) extends FailureStrategy
  }

  sealed trait TransitionState

  object TransitionState {
    case class FailedTransition(failureTime: Long,
                                failureCount: Int,
                                failureReason: String,
                                failureStrategy: FailureStrategy
                               ) extends TransitionState
    case object ActiveTransition extends TransitionState
  }

  sealed trait TransitionEvent {
    val transitionFiringId: Long
    val transitionId: Long
  }

  object TransitionEvent {

    case class Fired(transitionFiringId: Long,
                     transitionId: Long,
                     timeStarted: Time,
                     timeCompleted: Time,
                     consumed: Marking[Long],
                     produced: Marking[Long],
                     output: EventInstance) extends TransitionEvent

    case class Failed(transitionFiringId: Long,
                      transitionId: Long,
                      correlationId: Option[String],
                      timeStarted: Time,
                      timeFailed: Time,
                      consume: Marking[Id],
                      input: Any,
                      failureReason: String,
                      exceptionStrategy: FailureStrategy) extends TransitionEvent
  }

  case class TransitionFiring(id: Long,
                              transition: Transition,
                              consume: Marking[Place],
                              input: EventInstance,
                              state: TransitionState = TransitionState.ActiveTransition) {

    def isActive: Boolean = state match {
      case TransitionState.FailedTransition(_, _, _, FailureStrategy.RetryWithDelay(_)) ⇒ true
      case TransitionState.ActiveTransition ⇒ true
      case _ ⇒ false
    }

    def isFailed: Boolean = state match {
      case _: TransitionState.FailedTransition => true
      case _ => false
    }

    def failureCount: Int = state match {
      case e: TransitionState.FailedTransition ⇒ e.failureCount
      case _ => 0
    }

    def execute: IO[TransitionEvent] = {
      val startTime = System.currentTimeMillis()
      val consumed: Marking[Id] = consume.marshall

      ???
      /*
      IO.unit.flatMap { _ =>
        // calling transitionTask(...) could potentially throw an exception
        // TODO I don't believe the last statement is true
        transitionTask(topology, transition)(job.consume, job.processState, job.input)
      }.map {
        case (producedMarking, out) ⇒
          TransitionFiredEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, producedMarking.marshall, out)
      }.handleException {
        // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
        case e: Throwable ⇒
          val failureCount = job.failureCount + 1
          val failureStrategy = handleException(job)(e, failureCount, startTime, topology.outMarking(transition))
          TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), failureStrategy)
      }.handleException {
        // If an exception was thrown while computing the failure strategy we block the interaction from firing
        case e: Throwable =>
          logger.error(s"Exception while handling transition failure", e)
          TransitionFailedEvent(job.id, transition.getId, job.correlationId, startTime, System.currentTimeMillis(), consumed, job.input, exceptionStackTrace(e), FailureStrategy.BlockTransition)
      }
       */
    }
  }
}

object BakerModel {

  type PetriNettyState = Marking[Place]

  case class RecipeInstanceState(
    recipeInstanceId: String,
    recipe: CompiledRecipe,
    //sequenceNr: Long,
    marking: PetriNettyState,
    ingredients: Map[String, Value],
    events: List[(Time, EventInstance)],
    firings: Map[Long, TransitionFiring]
    //receivedCorrelationIds: Set[String]
  ) {

    lazy val petriNet: RecipePetriNet = recipe.petriNet

    def reservedMarking: Marking[Place] =
      firings.map { case (_, firing) ⇒ firing.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

    def availableMarking: Marking[Place] =
      marking |-| reservedMarking

    def activeFirings: List[TransitionFiring] =
      firings.values.filter(_.isActive).toList

    def isBlocked(transition: Transition): Boolean =
      firings.values.exists(t => t.transition == transition && t.isFailed)

    def createFiring(transition: Transition, input: EventInstance): (RecipeInstanceState, Either[String, TransitionFiring]) = {
      enabledParameters(availableMarking).get(transition) match {
        case None ⇒
          (this, Left(s"Not enough consumable tokens. This might have been caused because the event has already been fired up the the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired"))
        case Some(params) ⇒
          val firingId = Random.nextLong()
          val firing = TransitionFiring(firingId, transition, params.head, input)
          val updatedInstance = copy(firings = firings + (firing.id -> firing))
          (updatedInstance, Right(firing))
      }
    }

    def isEnabled(t: Transition, ofMarking: Marking[Place]): Boolean =
      consumableMarkings(t, ofMarking).nonEmpty

    def enabledTransitions(ofMarking: Marking[Place]): Iterable[Transition] =
      petriNet.transitions.filter(t => isEnabled(t, ofMarking))

    def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] =
      enabledTransitions(ofMarking).view.map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap

    def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
      // TODO this is not the most efficient, should break early when consumable tokens < edge weight
      val consumable = petriNet.inMarking(t).map {
        case (place, count) ⇒ (place, count, consumableTokens(place, ofMarking))
      }
      // check if any any places have an insufficient number of tokens
      if (consumable.exists {case (_, count, tokens) ⇒ tokens.multisetSize < count})
        Seq.empty
      else {
        val consume = consumable.map {
          case (place, count, tokens) ⇒ place -> MultiSet.copyOff[Any](tokens.allElements.take(count))
        }.toMarking

        // TODO lazily compute all permutations instead of only providing the first result
        Seq(consume)
      }
    }

    def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] = ofMarking.getOrElse(p, MultiSet.empty)
  }

  object RecipeInstanceState {

    def empty(recipe: CompiledRecipe, recipeInstanceId: String): RecipeInstanceState =
      RecipeInstanceState(
        recipe = recipe,
        marking = recipe.initialMarking,
        recipeInstanceId = recipeInstanceId,
        ingredients = Map.empty,
        events = List.empty,
        firings = Map.empty
      )
  }

  type Time = Int

  trait FutureModel {
    type Output
    val input: ModelState
    val model: Model[Output]

    def run: (ModelState, ModelFailure[Output]) =
      model.run(input).value
  }

  case class ModelState(time: Time,
                        next: List[FutureModel],
                        randomSeed: Int,
                        recipes: Map[String, (Time, CompiledRecipe)],
                        recipeInstances: Map[String, RecipeInstanceState]
                       ) { self =>

    def moveTime: ModelState =
      copy(time = time + 1)

    def async[A](_model: Model[A]): ModelState =
      copy(next = new FutureModel { type Output = A; val model: Model[A] = _model; val input: ModelState = self } :: next)

    def nextLong: (ModelState, Long) = {
      val last = new Random(randomSeed)
      val newSeed = last.nextInt(Int.MaxValue)
      (copy(randomSeed = newSeed), new Random(newSeed).nextLong())
    }

    def addRecipe(recipe: CompiledRecipe): ModelState =
      copy(recipes = recipes + (recipe.recipeId -> (time, recipe)))

    def bake(recipe: CompiledRecipe, recipeInstanceId: String): ModelState =
      copy(recipeInstances = recipeInstances + (recipeInstanceId -> RecipeInstanceState.empty(recipe, recipeInstanceId)))
  }

  type ModelFailure[A] = Either[BakerException, A]

  type Model[A] = State[ModelState, ModelFailure[A]]

  def async[A](run: ModelState => (ModelState, ModelFailure[A])): Model[A] =
    ???
    //State.modify[ModelState](_.async(State(run)))

  def validate[A](f: ModelState => ModelFailure[A]): Model[A] =
    ???

  def fail[A](exception: BakerException): Model[A] =
    State.pure(Left(exception))

  def failF[A](exception: BakerException)(state0: ModelState): (ModelState, Either[BakerException, A]) =
    (state0, Left(exception))
}

class BakerModel extends Baker[BakerModel.Model] {

  override def addRecipe(compiledRecipe: CompiledRecipe): Model[String] = async { model =>
    (model.addRecipe(compiledRecipe), Right(compiledRecipe.recipeId))
  }

  override def getRecipe(recipeId: String): Model[RecipeInformation] = State { model =>
    (model, model.recipes.get(recipeId) match {
      case None => Left(NoSuchRecipeException(recipeId))
      case Some((timestamp, recipe)) => Right(RecipeInformation(recipe, timestamp, Set.empty)) // Implementation errors are going to be removed
    })
  }

  override def getAllRecipes: Model[Map[String, RecipeInformation]] = State { model =>
    ???
  }

  override def addInteractionInstance(implementation: InteractionInstance): Model[Unit] =
    ???

  override def bake(recipeId: String, recipeInstanceId: String): Model[Unit] = State { model =>
    (model.recipes.get(recipeId), model.recipeInstances.get(recipeInstanceId)) match {
      case (Some((_, recipe)), None) =>
        (model.bake(recipe, recipeInstanceId), Right(Unit))
      case (_, Some(_)) =>
        failF(ProcessAlreadyExistsException(recipeInstanceId))(model)
      case (None, _) =>
        failF(NoSuchRecipeException(recipeId))(model)
    }
  }

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): Model[SensoryEventResult] =
    State { model =>
      val validation: Either[BakerException, (RecipeInstanceState, Transition)] =
        for {
          recipeInstanceState <- model.recipeInstances.get(recipeInstanceId)
            .toRight(NoSuchProcessException(recipeInstanceId))
          transition <- recipeInstanceState.recipe.petriNet.transitions.find(_.label == event.name)
            .toRight(IllegalEventException(s"No event with name '${event.name}' found in recipe '${recipeInstanceState.recipe.name}'"))
          sensoryEventDescriptor <- recipeInstanceState.recipe.sensoryEvents.find(_.name == event.name)
            .toRight(IllegalEventException(s"No event with name '${event.name}' found in recipe '${recipeInstanceState.recipe.name}'"))
          _ <- {
            val errors = event.validate(sensoryEventDescriptor)
            if (errors.nonEmpty) Left(IllegalEventException(s"Invalid event: " + errors.mkString(",")))
            else Right(())
          }

          result = {
            if (recipeInstanceState.isBlocked(transition))
              (recipeInstanceState, SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
            else {
              recipeInstanceState.createFiring(transition, event) match {
                case (nextState, Left(_)) =>
                  (nextState, SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
                case (nextState, Right(transitionFiring)) =>
                  ()
              }
            }
          }
        } yield (recipeInstanceState, transition)

      ???
  }

  /*
  processIndexActor.ask(ProcessEvent(
    recipeInstanceId = recipeInstanceId,
    event = event,
    correlationId = correlationId,
    timeout = config.timeouts.defaultProcessEventTimeout,
    reaction = FireSensoryEventReaction.NotifyWhenCompleted(waitForRetries = true)
  ))(config.timeouts.defaultProcessEventTimeout).flatMap {
    case FireSensoryEventRejection.InvalidEvent(_, message) =>
      Future.failed(IllegalEventException(message))
    case FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId0) =>
      Future.failed(NoSuchProcessException(recipeInstanceId0))
    case _: FireSensoryEventRejection.FiringLimitMet =>
      Future.successful(SensoryEventResult(SensoryEventStatus.FiringLimitMet, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.AlreadyReceived =>
      Future.successful(SensoryEventResult(SensoryEventStatus.AlreadyReceived, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.ReceivePeriodExpired =>
      Future.successful(SensoryEventResult(SensoryEventStatus.ReceivePeriodExpired, Seq.empty, Map.empty))
    case _: FireSensoryEventRejection.RecipeInstanceDeleted =>
      Future.successful(SensoryEventResult(SensoryEventStatus.RecipeInstanceDeleted, Seq.empty, Map.empty))
    case ProcessEventCompletedResponse(result) =>
      Future.successful(result)
  }
   */

}