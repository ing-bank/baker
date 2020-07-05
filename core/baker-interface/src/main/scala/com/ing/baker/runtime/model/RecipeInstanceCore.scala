package com.ing.baker.runtime.model

import java.io.{PrintWriter, StringWriter}
import java.lang.reflect.InvocationTargetException

import cats.effect.{Async, Clock}
import cats.implicits._
import com.ing.baker.il
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, EventOutputTransformer, IngredientDescriptor}
import com.ing.baker.petrinet.api.{Marking, MultiSet, _}
import com.ing.baker.runtime.model.FailureStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.model.RecipeInstanceCore.FatalInteractionException
import com.ing.baker.runtime.model.RecipeInstanceManager.FireSensoryEventRejection
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.types.{PrimitiveValue, Value}
import org.slf4j.MDC

import scala.util.Random

case class RecipeInstanceCore[F[_]](
    recipeInstanceId: String,
    recipe: CompiledRecipe,
    sequenceNumber: Long,
    marking: Marking[Place],
    ingredients: Map[String, Value],
    events: List[(Int, EventInstance)],
    firings: Map[Long, TransitionFiring],
    receivedCorrelationIds: Set[String],
    interactionManager: InteractionManager[F]
  )(implicit effect: Async[F], clock: Clock[F]) {

  lazy val petriNet: RecipePetriNet = recipe.petriNet

  def fireTransition(transitionId: Long, input: EventInstance, correlationId: Option[String] = None): Either[(FireSensoryEventRejection, String), (RecipeInstanceCore[F], F[TransitionEvent])] = {

    def fireTransitionMain: FireTransitionValidation[(RecipeInstanceCore[F], F[TransitionEvent])] =
      for {
        _ <- validateReceivedCorrelationId
        _ <- validateIsBlocked
        params <- validateConsumableTokens
        firing = TransitionFiring(Random.nextLong(), correlationId, transition, params.head, input)
        updatedInstance = copy(firings = firings + (firing.id -> firing))
        //TODO log.firingTransition(recipeInstanceId, job.id, job.transition.asInstanceOf[Transition], System.currentTimeMillis())
      } yield updatedInstance -> runFiring(firing)

    type FireTransitionValidation[+A] =
      Either[(FireSensoryEventRejection, String), A]
    def reject[A](rejection: FireSensoryEventRejection, explanation: String): FireTransitionValidation[A] =
      Left(rejection -> explanation)
    def accept[A](a: A): FireTransitionValidation[A] =
      Right(a)
    def continue: FireTransitionValidation[Unit] =
      accept(())
    def transition =
      petriNet.transitions.getById(transitionId, "transition in petrinet")

    def validateReceivedCorrelationId: FireTransitionValidation[Unit] =
      correlationId match {
        case Some(correlationId) if receivedCorrelationIds.contains(correlationId) || firings.values.exists(_.correlationId.contains(correlationId)) =>
          reject(FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId), s"The correlation id $correlationId was previously received by another fire transition command")
        case _ => continue
      }

    def validateIsBlocked: FireTransitionValidation[Unit] =
      if (isBlocked(transition)) reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), "Transition is blocked by a previous failure")
      else continue

    def validateConsumableTokens: FireTransitionValidation[Iterable[Marking[Place]]] =
      enabledParameters(availableMarking).get(transition) match {
        case None ⇒
          reject(FireSensoryEventRejection.FiringLimitMet(recipeInstanceId), s"Not enough consumable tokens. This might have been caused because the event has already been fired up to the firing limit but the recipe requires more instances of the event, use withSensoryEventNoFiringLimit or increase the amount of firing limit on the recipe if such behaviour is desired")
        case Some(params) ⇒
          accept(params)
      }

    def runFiring(transitionFiring: TransitionFiring): F[TransitionEvent] = {

      def exceptionStackTrace(e: Throwable): String = {
        val sw = new StringWriter()
        e.printStackTrace(new PrintWriter(sw))
        sw.toString
      }

      def runFiringMain: F[TransitionEvent] = for {
        startTime <- clock.realTime(scala.concurrent.duration.MILLISECONDS)
        transition = transitionFiring.transition
        consumed = transitionFiring.consume.marshall
        transitionEvent <- runTransition(transition)
          .flatMap[TransitionEvent] { case (producedMarking, output) =>
            clock.realTime(scala.concurrent.duration.MILLISECONDS).map { endTime =>
              TransitionEvent.Fired(
                transitionFiring.id,
                transition.getId,
                transitionFiring.correlationId,
                startTime,
                endTime,
                consumed,
                producedMarking.marshall,
                output
              )
            }
          // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
          }.handleError { e ⇒
            val failureCount = transitionFiring.failureCount + 1
            val failureStrategy = handleException(e, failureCount, startTime, petriNet.outMarking(transition))
            TransitionEvent.Failed(transitionFiring.id, transition.getId, transitionFiring.correlationId, startTime, System.currentTimeMillis(), consumed, transitionFiring.input, exceptionStackTrace(e), failureStrategy)
          // If an exception was thrown while computing the failure strategy we block the interaction from firing
          }.handleError { e =>
            //TODO logger.error(s"Exception while handling transition failure", e)
            TransitionEvent.Failed(transitionFiring.id, transition.getId, transitionFiring.correlationId, startTime, System.currentTimeMillis(), consumed, transitionFiring.input, exceptionStackTrace(e), FailureStrategy.BlockTransition)
          }
      } yield transitionEvent

      def runTransition(transition: Transition): F[(Marking[Place], EventInstance)] = {

        def runTransitionMain: F[(Marking[Place], EventInstance)] =
          transition match {
            case interactionTransition: InteractionTransition => runInteractionTransition(interactionTransition, petriNet.outMarking(interactionTransition))
            case eventTransition: EventTransition => effect.pure(petriNet.outMarking(eventTransition).toMarking, input)
            case otherTransition => effect.pure(petriNet.outMarking(otherTransition).toMarking, null.asInstanceOf[EventInstance])
          }

        def runInteractionTransition(interaction: InteractionTransition, outAdjacent: MultiSet[Place]): F[(Marking[Place], EventInstance)] = {

          def runInteractionTransitionMain: F[(Marking[Place], EventInstance)] = {
            MDC.put("RecipeInstanceId", recipeInstanceId)
            MDC.put("recipeName", recipe.name)
            (
              for {
                timeStarted <- clock.realTime(scala.concurrent.duration.MILLISECONDS)
                //TODO eventStream.publish(InteractionStarted(timeStarted, recipe.name, recipe.recipeId, recipeInstanceId, interaction.interactionName))
                interactionOutput <- interactionManager.executeImplementation(interaction, interactionInput)
                _ <- validateInteractionOutput(interactionOutput)
                transformedOutput = transformEventWithTheInteractionTransitionOutputTransformers(interactionOutput)
                timeCompleted <- clock.realTime(scala.concurrent.duration.MILLISECONDS)
                //TODO eventStream.publish(InteractionCompleted(timeCompleted, timeCompleted - timeStarted, recipe.name, recipe.recipeId, processState.recipeInstanceId, interaction.interactionName, outputEvent))
                outputMarking = createOutputMarkingForPetriNet(outAdjacent, transformedOutput)
              } yield (outputMarking, transformedOutput.orNull)
              ).handleErrorWith { e =>
              MDC.remove("RecipeInstanceId")
              MDC.remove("recipeName")
              e match {
                case e: InvocationTargetException =>
                  effect.raiseError(e.getCause)
                case e: Throwable =>
                  effect.raiseError(e)
              }
            }
          }

          def interactionInput: Seq[IngredientInstance] = {
            // the process id is a special ingredient that is always available
            val recipeInstanceId: (String, Value) = il.recipeInstanceIdName -> PrimitiveValue(recipeInstanceId)
            val processId: (String, Value) = il.processIdName -> PrimitiveValue(recipeInstanceId)
            // a map of all ingredients
            val allIngredients: Map[String, Value] = interaction.predefinedParameters ++ ingredients + recipeInstanceId + processId
            // arranges the ingredients in the expected order
            interaction.requiredIngredients.map {
              case IngredientDescriptor(name, _) =>
                IngredientInstance(name, allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'")))
            }
          }

          def validateInteractionOutput(interactionOutput: Option[EventInstance]): F[Unit] = {
            def fail(message: String): F[Unit] = effect.raiseError(new FatalInteractionException(message))
            def continue: F[Unit] = effect.unit
            interactionOutput match {
              case None =>
                if (interaction.eventsToFire.nonEmpty)
                  fail(s"Interaction '${interaction.interactionName}' did not provide any output, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")
                else
                  continue
              case Some(event) =>
                val nullIngredientNames = event.providedIngredients.collect { case (name, null) => name }
                // null values for ingredients are NOT allowed
                if (nullIngredientNames.nonEmpty)
                  fail(s"Interaction '${interaction.interactionName}' returned null for the following ingredients: ${nullIngredientNames.mkString(",")}")
                else
                // the event name must match an event name from the interaction output
                  interaction.originalEvents.find(_.name == event.name) match {
                    case None =>
                      fail(s"Interaction '${interaction.interactionName}' returned unknown event '${event.name}, expected one of: ${interaction.eventsToFire.map(_.name).mkString(",")}")
                    case Some(eventType) =>
                      val errors = event.validate(eventType)
                      if (errors.nonEmpty)
                        fail(s"Event '${event.name}' does not match the expected type: ${errors.mkString}")
                      else
                        continue
                  }
            }
          }

          def transformEventWithTheInteractionTransitionOutputTransformers(interactionOutput: Option[EventInstance]): Option[EventInstance] = {
            def eventOutputTransformer(eventInstance: EventInstance): Option[(String, EventOutputTransformer)] =
              interaction.eventOutputTransformers.find { case (eventName, _) => eventInstance.name.equals(eventName) }
            interactionOutput.map { eventInstance =>
              eventOutputTransformer(eventInstance) match {
                case Some((_, eventOutputTransformer)) =>
                  EventInstance(
                    eventOutputTransformer.newEventName,
                    eventInstance.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
                case None => eventInstance
              }
            }
          }

          runInteractionTransitionMain
        }

        runTransitionMain
      }

      def handleException(throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place]): FailureStrategy = {
        if (throwable.isInstanceOf[Error])
          BlockTransition
        else
          transitionFiring.transition match {
            case interaction: InteractionTransition =>
              // compute the interaction failure strategy outcome
              val failureStrategyOutcome = interaction.failureStrategy.apply(failureCount)
              val currentTime = System.currentTimeMillis()
              //TODO eventStream.publish(InteractionFailed(currentTime, currentTime - startTime, recipe.name, recipe.recipeId, transitionFiring.processState.recipeInstanceId, transitionFiring.transition.label, failureCount, throwable, failureStrategyOutcome))
              // translates the recipe failure strategy to a petri net failure strategy
              failureStrategyOutcome match {
                case ExceptionStrategyOutcome.BlockTransition => BlockTransition
                case ExceptionStrategyOutcome.RetryWithDelay(delay) => RetryWithDelay(delay)
                case ExceptionStrategyOutcome.Continue(eventName) =>
                  val runtimeEvent = EventInstance(eventName, Map.empty)
                  Continue(createOutputMarkingForPetriNet(outMarking, Some(runtimeEvent)), runtimeEvent)
              }
            case _ => BlockTransition
          }
      }

      def createOutputMarkingForPetriNet(outAdjacent: MultiSet[Place], interactionOutput: Option[EventInstance]): Marking[Place] =
        outAdjacent.keys.map { place =>
          // use the event name as a token value, otherwise null
          val value: Any = interactionOutput.map(_.name).orNull
          place -> MultiSet.copyOff(Seq(value))
        }.toMarking

      runFiringMain
    }

    fireTransitionMain
  }

  private def reservedMarking: Marking[Place] =
    firings.map { case (_, firing) ⇒ firing.consume }.reduceOption(_ |+| _).getOrElse(Marking.empty)

  private def availableMarking: Marking[Place] =
    marking |-| reservedMarking

  private def activeFirings: List[TransitionFiring] =
    firings.values.filter(_.isActive).toList

  private def isBlocked(transition: Transition): Boolean =
    firings.values.exists(t => t.transition == transition && t.isFailed)

  private def enabledParameters(ofMarking: Marking[Place]): Map[Transition, Iterable[Marking[Place]]] = {

    def enabledTransitions(ofMarking: Marking[Place]): Set[Transition] =
      petriNet.transitions.filter(t => consumableMarkings(t, ofMarking).nonEmpty)

    enabledTransitions(ofMarking).map(t ⇒ t -> consumableMarkings(t, ofMarking)).toMap
  }

  private def consumableMarkings(t: Transition, ofMarking: Marking[Place]): Iterable[Marking[Place]] = {
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

  private def consumableTokens(p: Place, ofMarking: Marking[Place]): MultiSet[Any] = ofMarking.getOrElse(p, MultiSet.empty)
}

object RecipeInstanceCore {

  class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)

  def empty[F[_]](recipe: CompiledRecipe, recipeInstanceId: String, interactionManager: InteractionManager[F])(implicit effect: Async[F], clock: Clock[F]): RecipeInstanceCore[F] =
    RecipeInstanceCore[F](
      recipe = recipe,
      marking = recipe.initialMarking,
      sequenceNumber = 0,
      recipeInstanceId = recipeInstanceId,
      ingredients = Map.empty,
      events = List.empty,
      firings = Map.empty,
      receivedCorrelationIds = Set.empty,
      interactionManager = interactionManager
    )
}
