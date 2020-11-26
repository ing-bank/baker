package com.ing.baker.runtime.model.recipeinstance

import java.io.{PrintWriter, StringWriter}
import java.lang.reflect.InvocationTargetException

import cats.effect.{Sync, Timer}
import cats.implicits._
import com.ing.baker.il
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, IngredientDescriptor}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.types.{PrimitiveValue, Value}
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.duration.MILLISECONDS
import scala.util.Random

object TransitionExecution {

  def generateId: Long = Random.nextLong()

  sealed trait State

  object State {

    case class Failed(failureTime: Long, failureCount: Int, failureStrategy: ExceptionStrategyOutcome) extends State

    case object Active extends State
  }

  sealed trait Outcome

  object Outcome {

    case class Completed(timeStarted: Long, timeCompleted: Long, output: Option[EventInstance]) extends Outcome

    case class Failed(timeStarted: Long, timeFailed: Long, exceptionStrategy: ExceptionStrategyOutcome) extends Outcome
  }
}

/** A data structure representing the properties and state of progression of a recipe instance; it might represent an
  * internal event firing or an interaction execution
  */
private[recipeinstance] case class TransitionExecution(
  id: Long = TransitionExecution.generateId,
  recipeInstanceId: String,
  recipe: CompiledRecipe,
  transition: Transition,
  consume: Marking[Place],
  input: Option[EventInstance], // TODO maybe this and ingredients can be moved to the execution part?
  ingredients: Map[String, Value],
  correlationId: Option[String],
  state: TransitionExecution.State = TransitionExecution.State.Active
) extends LazyLogging {

  def isInactive: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, ExceptionStrategyOutcome.RetryWithDelay(_)) ⇒ false
      case TransitionExecution.State.Active ⇒ false
      case _ ⇒ true
    }

  def isRetrying: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, ExceptionStrategyOutcome.RetryWithDelay(_)) => true
      case _ => false
    }

  def isBlocked: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, ExceptionStrategyOutcome.BlockTransition) => true
      case _ => false
    }

  def failureCount: Int =
    state match {
      case e: TransitionExecution.State.Failed ⇒ e.failureCount
      case _ => 0
    }

  def toFailedState(failedOutcome: TransitionExecution.Outcome.Failed): TransitionExecution =
    copy(state = TransitionExecution.State.Failed(
      failedOutcome.timeFailed, failureCount + 1, failedOutcome.exceptionStrategy))

  def execute[F[_]](implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome] =
    for {
      startTime <- timer.clock.realTime(MILLISECONDS)
      result <- effect.attempt {
        transition match {
          case interactionTransition: InteractionTransition =>
            executeInteractionInstance(interactionTransition)
          case _: EventTransition =>
            effect.pure(input)
          case _ =>
            effect.pure(None)
        }
      }
      endTime <- timer.clock.realTime(MILLISECONDS)
      outcome = result match {
        case Left(throwable) =>
          buildFailedOutcome(startTime, endTime, throwable)
        case Right(output) =>
          buildCompletedOutcome(startTime, endTime, output)
      }
    } yield outcome

  private def buildCompletedOutcome(startTime: Long, endTime: Long, output: Option[EventInstance]): TransitionExecution.Outcome =
    TransitionExecution.Outcome.Completed(startTime, endTime, output)

  /* TODO when at point of documenting this is still commented then delete
  def exceptionStackTrace(throwable: Throwable): String = {
    val sw = new StringWriter()
    throwable.printStackTrace(new PrintWriter(sw))
    sw.toString
  }
   */

  private def buildFailedOutcome(startTime: Long, endTime: Long, e: Throwable): TransitionExecution.Outcome = {
    val throwable = e match {
      case e: InvocationTargetException => e.getCause
      case e => e
    }
    val failureReactionStrategy =
      (throwable, transition) match {
        case (e, _) if e.isInstanceOf[Error] =>
          ExceptionStrategyOutcome.BlockTransition
        case (_, interaction: InteractionTransition) =>
          interaction.failureStrategy.apply(failureCount + 1)
        case _ =>
          ExceptionStrategyOutcome.BlockTransition
      }
    TransitionExecution.Outcome.Failed(startTime, endTime, failureReactionStrategy)
  }

  def producedMarking(interactionOutput: Option[EventInstance]): Marking[Place] =
    recipe.petriNet.outMarking(transition).keys.map { place =>
      val value: Any = interactionOutput.map(_.name).orNull
      place -> MultiSet.copyOff(Seq(value))
    }.toMarking

  def buildOutcomeForStopRetryingInteraction[F[_]](implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Failed] =
    if (isRetrying)
      for {
        timestamp <- timer.clock.realTime(MILLISECONDS)
        outcome = TransitionExecution.Outcome.Failed(
          timestamp,
          timestamp,
          ExceptionStrategyOutcome.BlockTransition)
      } yield outcome
    else effect.raiseError(new FatalInteractionException("Interaction is not retrying"))

  def buildOutcomeForRetryingBlockedInteraction[F[_]](implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Failed] =
    if (isBlocked)
      for {
        timestamp <- timer.clock.realTime(MILLISECONDS)
        outcome = TransitionExecution.Outcome.Failed(
          timestamp,
          timestamp,
          ExceptionStrategyOutcome.RetryWithDelay(0))
      } yield outcome
    else effect.raiseError(new FatalInteractionException("Interaction is not blocked"))

  def buildOutcomeForResolvingBlockedInteraction[F[_]](eventInstance: EventInstance)(implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Completed] =
    (isBlocked, transition) match {
      case (true, interactionTransition: InteractionTransition) =>
        for {
          _ <- validateInteractionOutput[F](interactionTransition, Some(eventInstance))
          transformedEvent: Option[EventInstance] = transformOutputWithTheInteractionTransitionOutputTransformers(interactionTransition, Some(eventInstance))
          timestamp <- timer.clock.realTime(MILLISECONDS)
          outcome = TransitionExecution.Outcome.Completed(
            timestamp,
            timestamp,
            transformedEvent
          )
        } yield outcome
      case (false, _) =>
        effect.raiseError(new FatalInteractionException("Interaction is not blocked"))
      case _ =>
        effect.raiseError(new FatalInteractionException("TransitionExecution is not for an Interaction"))
    }

  private def executeInteractionInstance[F[_]](interactionTransition: InteractionTransition)(implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[Option[EventInstance]] = {

    def buildInteractionInput: Seq[IngredientInstance] = {
      val recipeInstanceIdIngredient: (String, Value) = il.recipeInstanceIdName -> PrimitiveValue(recipeInstanceId)
      val processIdIngredient: (String, Value) = il.processIdName -> PrimitiveValue(recipeInstanceId)
      val allIngredients: Map[String, Value] = ingredients ++ interactionTransition.predefinedParameters + recipeInstanceIdIngredient + processIdIngredient
      interactionTransition.requiredIngredients.map {
        case IngredientDescriptor(name, _) =>
          IngredientInstance(name, allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'")))
      }
    }

    for {
      startTime <- timer.clock.realTime(MILLISECONDS)
      _ <- components.eventStream.publish(InteractionStarted(
        startTime, recipe.name, recipe.recipeId,
        recipeInstanceId, interactionTransition.interactionName))
      outcome <- {
        for {
          interactionOutput <- components.interactionInstanceManager.execute(interactionTransition, buildInteractionInput)
          _ <- validateInteractionOutput(interactionTransition, interactionOutput)
          transformedOutput = transformOutputWithTheInteractionTransitionOutputTransformers(interactionTransition, interactionOutput)
          endTime <- timer.clock.realTime(MILLISECONDS)
          _ <- components.eventStream.publish(InteractionCompleted(
            endTime, endTime - startTime, recipe.name, recipe.recipeId, recipeInstanceId,
            interactionTransition.interactionName, transformedOutput))
        } yield transformedOutput
      }.onError { case e: Throwable =>
        val throwable = e match {
          case e: InvocationTargetException => e.getCause
          case e => e
        }
        for {
          endTime <- timer.clock.realTime(MILLISECONDS)
          _ <- components.eventStream.publish(InteractionFailed(
            endTime, endTime - startTime, recipe.name, recipe.recipeId, recipeInstanceId,
            transition.label, failureCount, throwable, interactionTransition.failureStrategy.apply(failureCount + 1)))
        } yield ()
      }
    } yield outcome
  }

  private def validateInteractionOutput[F[_]](interactionTransition: InteractionTransition, interactionOutput: Option[EventInstance])(implicit effect: Sync[F]): F[Unit] = {
    def fail(message: String): F[Unit] = effect.raiseError(new FatalInteractionException(message))
    def continue: F[Unit] = effect.unit
    interactionOutput match {
      case None if interactionTransition.eventsToFire.nonEmpty =>
        fail(s"Interaction '${interactionTransition.interactionName}' did not provide any output, expected one of: ${interactionTransition.eventsToFire.map(_.name).mkString(",")}")
      case Some(event) if event.providedIngredients.collect { case (name, null) => name }.nonEmpty =>
        fail(s"Interaction '${interactionTransition.interactionName}' returned null for ingredients")
      case Some(event) =>
        interactionTransition.originalEvents.find(_.name == event.name) match {
          case None =>
            fail(s"Interaction '${interactionTransition.interactionName}' returned unknown event '${event.name}, expected one of: ${interactionTransition.eventsToFire.map(_.name).mkString(",")}")
          case Some(eventType) =>
            val errors = event.validate(eventType)
            if (errors.nonEmpty)
              fail(s"Event '${event.name}' does not match the expected type: ${errors.mkString}")
            else
              continue
        }
      case _ => continue
    }
  }

  private def transformOutputWithTheInteractionTransitionOutputTransformers(interactionTransition: InteractionTransition, interactionOutput: Option[EventInstance]): Option[EventInstance] = {
    interactionOutput.map { eventInstance =>
      val eventOutputTransformer =
        interactionTransition.eventOutputTransformers.find { case (eventName, _) => eventInstance.name.equals(eventName) }
      eventOutputTransformer match {
        case Some((_, eventOutputTransformer)) =>
          EventInstance(
            eventOutputTransformer.newEventName,
            eventInstance.providedIngredients.map { case (name, value) => eventOutputTransformer.ingredientRenames.getOrElse(name, name) -> value })
        case None => eventInstance
      }
    }
  }
}
