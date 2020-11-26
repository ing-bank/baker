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
import com.ing.baker.runtime.model.recipeinstance.FailureStrategy.{BlockTransition, Continue, RetryWithDelay}
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

    case class Failed(failureTime: Long, failureCount: Int, failureReason: String, failureStrategy: FailureStrategy) extends State

    case object Active extends State
  }

  sealed trait Outcome

  object Outcome {

    case class Completed(timeStarted: Long, timeCompleted: Long, produced: Marking[Place], output: Option[EventInstance]) extends Outcome

    case class Failed(timeStarted: Long, timeFailed: Long, failureReason: String, exceptionStrategy: FailureStrategy) extends Outcome
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
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.RetryWithDelay(_)) ⇒ false
      case TransitionExecution.State.Active ⇒ false
      case _ ⇒ true
    }

  def isRetrying: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.RetryWithDelay(_)) => true
      case _ => false
    }

  def isBlocked: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.BlockTransition) => true
      case _ => false
    }

  def failureCount: Int =
    state match {
      case e: TransitionExecution.State.Failed ⇒ e.failureCount
      case _ => 0
    }

  def toFailedState(failedOutcome: TransitionExecution.Outcome.Failed): TransitionExecution =
    copy(state = TransitionExecution.State.Failed(
      failedOutcome.timeFailed, failureCount + 1, failedOutcome.failureReason, failedOutcome.exceptionStrategy))

  def execute[F[_]](implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome] =
    for {
      startTime <- timer.clock.realTime(MILLISECONDS)
      result <- effect.attempt {
        transition match {
          case interactionTransition: InteractionTransition =>
            executeInteractionInstance(interactionTransition)
          case eventTransition: EventTransition =>
            effect.pure(recipe.petriNet.outMarking(eventTransition).toMarking, input)
          case otherTransition =>
            effect.pure(recipe.petriNet.outMarking(otherTransition).toMarking, None)
        }
      }
      endTime <- timer.clock.realTime(MILLISECONDS)
      outcome = result match {
        case Left(throwable) =>
          buildFailedOutcome(startTime, endTime, throwable)
        case Right((producedMarking, output)) =>
          buildCompletedOutcome(startTime, endTime, producedMarking, output)
      }
    } yield outcome

  def buildOutcomeForStopRetryingInteraction[F[_]](implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Failed] =
    if (isRetrying)
      for {
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          timestamp,
          timestamp,
          failureReason,
          FailureStrategy.BlockTransition)
      } yield outcome
    else effect.raiseError(new FatalInteractionException("Interaction is not retrying"))

  def buildOutcomeForRetryingBlockedInteraction[F[_]](implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Failed] =
    if (isBlocked)
      for {
        timestamp <- timer.clock.realTime(MILLISECONDS)
        failureReason <- getFailureReason
        outcome = TransitionExecution.Outcome.Failed(
          timestamp,
          timestamp,
          failureReason,
          FailureStrategy.RetryWithDelay(0))
      } yield outcome
    else effect.raiseError(new FatalInteractionException("Interaction is not blocked"))

  def buildOutcomeForResolvingBlockedInteraction[F[_]](eventInstance: EventInstance)(implicit effect: Sync[F], timer: Timer[F]): F[TransitionExecution.Outcome.Completed] =
    (isBlocked, transition) match {
      case (true, interactionTransition: InteractionTransition) =>
        for {
          _ <- validateInteractionOutput[F](interactionTransition, Some(eventInstance))
          producedMarking: Marking[Place] = createOutputMarking(recipe.petriNet.outMarking(interactionTransition), Some(eventInstance))
          transformedEvent: Option[EventInstance] = transformOutputWithTheInteractionTransitionOutputTransformers(interactionTransition, Some(eventInstance))
          timestamp <- timer.clock.realTime(MILLISECONDS)
          outcome = TransitionExecution.Outcome.Completed(
            timestamp,
            timestamp,
            producedMarking,
            transformedEvent
          )
        } yield outcome
      case (false, _) =>
        effect.raiseError(new FatalInteractionException("Interaction is not blocked"))
      case _ =>
        effect.raiseError(new FatalInteractionException("TransitionExecution is not for an Interaction"))
    }

  private def executeInteractionInstance[F[_]](interactionTransition: InteractionTransition)(implicit components: BakerComponents[F], effect: Sync[F], timer: Timer[F]): F[(Marking[Place], Option[EventInstance])] = {

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
          outputMarking = createOutputMarking(recipe.petriNet.outMarking(interactionTransition), transformedOutput)
          endTime <- timer.clock.realTime(MILLISECONDS)
          _ <- components.eventStream.publish(InteractionCompleted(
            endTime, endTime - startTime, recipe.name, recipe.recipeId, recipeInstanceId,
            interactionTransition.interactionName, transformedOutput))
        } yield (outputMarking, transformedOutput)
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

  private def buildCompletedOutcome(startTime: Long, endTime: Long, producedMarking: Marking[Place], output: Option[EventInstance]): TransitionExecution.Outcome =
    TransitionExecution.Outcome.Completed(startTime, endTime, producedMarking, output)

  private def buildFailedOutcome(startTime: Long, endTime: Long, e: Throwable): TransitionExecution.Outcome = {
    val throwable = e match {
      case e: InvocationTargetException => e.getCause
      case e => e
    }
    val exceptionStackTrace: String = {
      val sw = new StringWriter()
      throwable.printStackTrace(new PrintWriter(sw))
      sw.toString
    }
    val failureReactionStrategy =
      (throwable, transition) match {
        case (e, _) if e.isInstanceOf[Error] =>
          BlockTransition
        case (_, interaction: InteractionTransition) =>
          val interactionStrategy = interaction.failureStrategy.apply(failureCount + 1)
          interactionStrategy match {
            case ExceptionStrategyOutcome.BlockTransition =>
              BlockTransition
            case ExceptionStrategyOutcome.RetryWithDelay(delay) =>
              RetryWithDelay(delay)
            case ExceptionStrategyOutcome.Continue(eventName) =>
              val runtimeEvent = EventInstance(eventName, Map.empty)
              val outMarking = recipe.petriNet.outMarking(transition)
              Continue(createOutputMarking(outMarking, Some(runtimeEvent)), Some(runtimeEvent))
          }
        case _ =>
          BlockTransition
      }
    TransitionExecution.Outcome.Failed(startTime, endTime, exceptionStackTrace, failureReactionStrategy)
  }

  private def getFailureReason[F[_]](implicit effect: Sync[F]): F[String] =
    state match {
      case failure: TransitionExecution.State.Failed => effect.pure(failure.failureReason)
      case _ => effect.raiseError(new FatalInteractionException("This INTERNAL method should be called only after making sure this is a failed execution"))
    }

  private def createOutputMarking(outAdjacent: MultiSet[Place], interactionOutput: Option[EventInstance]): Marking[Place] =
    outAdjacent.keys.map { place =>
      val value: Any = interactionOutput.map(_.name).orNull
      place -> MultiSet.copyOff(Seq(value))
    }.toMarking

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
