package com.ing.baker.runtime.model.recipeinstance

import java.lang.reflect.InvocationTargetException
import cats.effect.{Effect, IO, Timer}
import cats.implicits._
import com.ing.baker.il
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, IngredientDescriptor}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.types.{ListValue, PrimitiveValue, RecordValue, Value}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.MDC

import scala.collection.immutable.{List, Seq}
import scala.concurrent.duration.MILLISECONDS
import scala.util.Random

object TransitionExecution {

  def generateId: Long = Random.nextLong()

  type Outcome = Either[ExceptionStrategyOutcome, Option[EventInstance]]

  sealed trait State

  object State {

    case class Failed(failureCount: Int, failureStrategy: ExceptionStrategyOutcome) extends State

    case object Active extends State
  }
}

/** A data structure that describes a single execution of a Recipe's transition, it contains everything the transition
  * needs to fire, including possible Interaction input event, current available ingredients, corresponding correlation
  * id etc.
  *
  * It is used by the RecipeInstance to execute each step of a recipe, once built the 'execute' method will run the
  * related transition, do proper validations on output, log and publish baker events, and return information to be
  * used by RecipeInstanceState.recordCompletedExecution to move the RecipeInstance state "forward".
  *
  * This data container is created in 2 locations:
  * 1) by the RecipeInstanceEventValidation.validateExecution method, which validates a sensory event and if valid
  * creates a new TransitionExecution.
  * 2) by the RecipeInstanceState.allEnabledExecutions, indirectly called when RecipeInstanceState.recordCompletedExecution
  * is called, such will create a TransitionExecution for each recipe transition which can be fired in consequence of
  * a previously executed TransitionExecution.
  */
private[recipeinstance] case class TransitionExecution(
  id: Long = TransitionExecution.generateId,
  recipeInstanceId: String,
  recipe: CompiledRecipe,
  transition: Transition,
  consume: Marking[Place],
  input: Option[EventInstance],
  ingredients: Map[String, Value],
  recipeInstanceMetadata: Map[String, String],
  eventList: List[EventMoment],
  correlationId: Option[String],
  state: TransitionExecution.State = TransitionExecution.State.Active,
  isReprovider: Boolean
) extends LazyLogging {

  def isInactive: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, ExceptionStrategyOutcome.RetryWithDelay(_)) => false
      case TransitionExecution.State.Active => false
      case _ => true
    }

  def isRetrying: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, ExceptionStrategyOutcome.RetryWithDelay(_)) => true
      case _ => false
    }

  def isBlocked: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, ExceptionStrategyOutcome.BlockTransition) => true
      case _ => false
    }

  def failureCount: Int =
    state match {
      case e: TransitionExecution.State.Failed => e.failureCount
      case _ => 0
    }

  def toFailedState(failureStrategy: ExceptionStrategyOutcome): TransitionExecution =
    copy(state = TransitionExecution.State.Failed(failureCount + 1, failureStrategy))

  def execute[F[_]](implicit components: BakerComponents[F], effect: Effect[F], timer: Timer[F]): F[TransitionExecution.Outcome] =
    for {
      result <- effect.attempt {
        transition match {
          case interactionTransition: InteractionTransition =>
            executeInteractionInstance(interactionTransition)
          case _: EventTransition =>
              for {
                timerstamp <- timer.clock.realTime(MILLISECONDS)
                _ <- effect.delay(components.logging.firingEvent(recipeInstanceId, "UNKNOWN", "UNKNOWN", id, transition, timerstamp))
              } yield input
          case _ =>
            effect.pure(None)
        }
      }
      outcome = result.leftMap { e =>
        val throwable = e match {
          case e: InvocationTargetException => e.getCause
          case e => e
        }
        (throwable, transition) match {
          case (e, _) if e.isInstanceOf[Error] =>
            ExceptionStrategyOutcome.BlockTransition
          case (_, interaction: InteractionTransition) =>
            interaction.failureStrategy.apply(failureCount + 1)
          case _ =>
            ExceptionStrategyOutcome.BlockTransition
        }
      }
    } yield outcome

  private def executeInteractionInstance[F[_]](interactionTransition: InteractionTransition)(implicit components: BakerComponents[F], effect: Effect[F], timer: Timer[F]): F[Option[EventInstance]] = {

    def buildInteractionInput: Seq[IngredientInstance] = {
      val recipeInstanceIdIngredient: (String, Value) = il.recipeInstanceIdName -> PrimitiveValue(recipeInstanceId)
      val processIdIngredient: (String, Value) = il.processIdName -> PrimitiveValue(recipeInstanceId)

      // Only map the recipeInstanceEventList if is it required, otherwise give an empty list
      val recipeInstanceEventList: (String, Value) =
        if(interactionTransition.requiredIngredients.exists(_.name == il.recipeInstanceEventListName))
          il.recipeInstanceEventListName -> ListValue(eventList.map(e => PrimitiveValue(e.name)))
        else
          il.recipeInstanceEventListName -> ListValue(List())

      val allIngredients: Map[String, Value] =
        ingredients ++
          interactionTransition.predefinedParameters +
          recipeInstanceIdIngredient +
          processIdIngredient +
          recipeInstanceEventList

      interactionTransition.requiredIngredients.map {
        case IngredientDescriptor(name, _) =>
          IngredientInstance(name, allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'")))
      }
    }

    def setupMdc: F[Unit] = effect.delay {
      MDC.put("recipeInstanceId", recipeInstanceId)
      MDC.put("recipeName", recipe.name)
    }

    def cleanMdc: F[Unit] = effect.delay {
      MDC.remove("recipeInstanceId")
      MDC.remove("recipeName")
    }

    def execute: F[Option[EventInstance]] =
      components.interactions.execute(
        interactionTransition,
        buildInteractionInput,
        Some(recipeInstanceMetadata))


    for {
      startTime <- timer.clock.realTime(MILLISECONDS)
      outcome <- {

        for {
          interactionStarted <- effect.delay(InteractionStarted(startTime, recipe.name, recipe.recipeId, recipeInstanceId, interactionTransition.interactionName))
          _ <- effect.delay(components.logging.interactionStarted(interactionStarted))
          _ <- components.eventStream.publish(interactionStarted)

          interactionOutput <- effect.bracket(setupMdc)(_ => execute)(_ => cleanMdc)
          _ <- validateInteractionOutput(interactionTransition, interactionOutput)
          transformedOutput = interactionOutput.map(_.transformWith(interactionTransition))

          endTime <- timer.clock.realTime(MILLISECONDS)

          interactionCompleted = InteractionCompleted(
            endTime, endTime - startTime, recipe.name, recipe.recipeId, recipeInstanceId,
            interactionTransition.interactionName, transformedOutput)
          _ <- effect.delay(components.logging.interactionFinished(interactionCompleted))
          _ <- components.eventStream.publish(interactionCompleted)

          _ <- transformedOutput match {
              case Some(event) =>
                val eventFired = EventFired(endTime, recipe.name, recipe.recipeId, recipeInstanceId, event)
                components.logging.eventFired(eventFired)
                components.eventStream.publish(eventFired)
              case None => effect.pure()
            }
        } yield transformedOutput

      }.onError { case e: Throwable =>

        val throwable = e match {
          case e: InvocationTargetException => e.getCause
          case e => e
        }
        for {
          endTime <- timer.clock.realTime(MILLISECONDS)
          interactionFailed = InteractionFailed(
            endTime, endTime - startTime, recipe.name, recipe.recipeId, recipeInstanceId,
            transition.label, failureCount, throwable, interactionTransition.failureStrategy.apply(failureCount + 1))
          _ <- effect.delay(components.logging.interactionFailed(interactionFailed))
          _ <- components.eventStream.publish(interactionFailed)
        } yield ()

      }
    } yield outcome
  }

  def validateEventForResolvingBlockedInteraction[F[_]](eventInstance: EventInstance)(implicit effect: Effect[F], timer: Timer[F]): F[EventInstance] =
    (isBlocked, transition) match {
      case (true, interactionTransition: InteractionTransition) =>
        validateInteractionOutput[F](interactionTransition, Some(eventInstance))
          .as(eventInstance.transformWith(interactionTransition))
      case (false, _) =>
        effect.raiseError(new FatalInteractionException("Interaction is not blocked"))
      case _ =>
        effect.raiseError(new FatalInteractionException("TransitionExecution is not for an Interaction"))
    }

  private def validateInteractionOutput[F[_]](interactionTransition: InteractionTransition, interactionOutput: Option[EventInstance])(implicit effect: Effect[F]): F[Unit] = {
    def fail(message: String): F[Unit] =
      effect.raiseError(new FatalInteractionException(message))
    interactionOutput match {
      case None if interactionTransition.eventsToFire.nonEmpty =>
        fail(s"Interaction '${interactionTransition.interactionName}' did not provide any output, expected one of: ${interactionTransition.eventsToFire.map(_.name).mkString(",")}")
      case None =>
        effect.unit
      case Some(event) =>
        event.validateAsOutputOf(interactionTransition).fold(effect.unit)(fail)
    }
  }
}
