package com.ing.baker.runtime.model.recipeinstance.execution

import java.io.{PrintWriter, StringWriter}
import java.lang.reflect.InvocationTargetException

import cats.effect.{Async, Sync, Timer}
import cats.implicits._
import com.ing.baker.il
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.il.petrinet._
import com.ing.baker.il.{CompiledRecipe, EventOutputTransformer, IngredientDescriptor}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.model.BakerComponents
import com.ing.baker.runtime.model.recipeinstance.FailureStrategy.{BlockTransition, Continue, RetryWithDelay}
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance.FatalInteractionException
import com.ing.baker.runtime.model.recipeinstance.FailureStrategy
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionCompleted, InteractionStarted}
import com.ing.baker.types.{PrimitiveValue, Value}
import com.typesafe.scalalogging.LazyLogging
import org.slf4j.MDC

import scala.concurrent.duration.MILLISECONDS
import scala.util.Random

object TransitionExecution {

  def generateId: Long = Random.nextLong()

  sealed trait State

  object State {

    case class Failed(failureTime: Long, failureCount: Int, failureReason: String, failureStrategy: FailureStrategy) extends State

    case object Active extends State
  }

  sealed trait Outcome { val transitionExecutionId: Long; val transitionId: Long }

  object Outcome {

    case class Completed(transitionExecutionId: Long,
                         transitionId: Long,
                         correlationId: Option[String],
                         timeStarted: Long,
                         timeCompleted: Long,
                         consumed: Marking[Long],
                         produced: Marking[Long],
                         output: Option[EventInstance]
                        ) extends Outcome

    case class Failed(transitionExecutionId: Long,
                      transitionId: Long,
                      correlationId: Option[String],
                      timeStarted: Long,
                      timeFailed: Long,
                      consume: Marking[Id],
                      input: Option[EventInstance],
                      failureReason: String,
                      exceptionStrategy: FailureStrategy
                     ) extends Outcome
  }
}

/** A data structure representing the properties and state of progression of a recipe instance; it might represent an
  * internal event firing or an interaction execution
  */
private[recipeinstance] case class TransitionExecution(
  id: Long = TransitionExecution.generateId,
  executionSequenceId: Long = -1,
  recipeInstanceId: String,
  recipe: CompiledRecipe,
  transition: Transition,
  consume: Marking[Place],
  input: Option[EventInstance],
  ingredients: Map[String, Value],
  correlationId: Option[String],
  state: TransitionExecution.State = TransitionExecution.State.Active
) extends LazyLogging {

  def setOwner(owner: Long): TransitionExecution =
    copy(executionSequenceId = owner)

  def isActive: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.RetryWithDelay(_)) ⇒
        true
      case TransitionExecution.State.Active ⇒
        true
      case _ ⇒
        false
    }

  def hasFailed: Boolean =
    state match {
      case _: TransitionExecution.State.Failed =>
        true
      case _ =>
        false
    }

  def isRetrying: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.RetryWithDelay(_)) =>
        true
      case _ =>
        false
    }

  def isBlocked: Boolean =
    state match {
      case TransitionExecution.State.Failed(_, _, _, FailureStrategy.BlockTransition) =>
        true
      case _ =>
        false
    }

  def getFailure[F[_]](implicit effect: Sync[F]): F[TransitionExecution.State.Failed] =
    state match {
      case failure: TransitionExecution.State.Failed =>
        effect.pure(failure)
      case _ =>
        effect.raiseError(new IllegalStateException("This INTERNAL method should be called only after making sure this is a failed execution"))
    }

  def getFailureReason[F[_]](implicit effect: Sync[F]): F[String] =
    getFailure.map(_.failureReason)

  def failureCount: Int =
    state match {
      case e: TransitionExecution.State.Failed ⇒ e.failureCount
      case _ => 0
    }

  def execute[F[_]](implicit components: BakerComponents[F], effect: Async[F], timer: Timer[F]): F[TransitionExecution.Outcome] = {
    // TODO maybe put log.transitionFired from the Process Instance here
    timer.clock.realTime(MILLISECONDS).flatMap { startTime =>
      //TODO log.firingTransition(recipeInstanceId, job.id, job.transition.asInstanceOf[Transition], System.currentTimeMillis())
      val execution: F[TransitionExecution.Outcome] =
        for {
          producedMarkingAndOutput <- enableTransition
          (producedMarking, output) = producedMarkingAndOutput
          endTime <- timer.clock.realTime(MILLISECONDS)
        } yield TransitionExecution.Outcome.Completed( id, transition.getId, correlationId, startTime, endTime, marshalMarking(consume), producedMarking.marshall, output )
      // In case an exception was thrown by the transition, we compute the failure strategy and return a TransitionFailedEvent
      execution.handleError { e ⇒
        val failureStrategy = handleInteractionInstanceException(e, failureCount + 1, startTime, recipe.petriNet.outMarking(transition))
        TransitionExecution.Outcome.Failed(id, transition.getId, correlationId, startTime, System.currentTimeMillis(), marshalMarking(consume), input, exceptionStackTrace(e), failureStrategy)
        // If an exception was thrown while computing the failure strategy we block the interaction from firing
      }.handleError { e =>
        logger.error(s"Exception while handling transition failure", e)
        TransitionExecution.Outcome.Failed(id, transition.getId, correlationId, startTime, System.currentTimeMillis(), marshalMarking(consume), input, exceptionStackTrace(e), FailureStrategy.BlockTransition)
      }
    }
  }

  def validateInteractionOutput[F[_]](interaction: InteractionTransition, interactionOutput: Option[EventInstance])(implicit effect: Async[F], timer: Timer[F]): F[Unit] = {
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

  def createOutputMarkingForPetriNet(outAdjacent: MultiSet[Place], interactionOutput: Option[EventInstance]): Marking[Place] =
    outAdjacent.keys.map { place =>
      // use the event name as a token value, otherwise null
      val value: Any = interactionOutput.map(_.name).orNull
      place -> MultiSet.copyOff(Seq(value))
    }.toMarking

  def transformOutputWithTheInteractionTransitionOutputTransformers(interaction: InteractionTransition, interactionOutput: Option[EventInstance]): Option[EventInstance] = {
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


  private def enableTransition[F[_]](implicit components: BakerComponents[F], effect: Async[F], timer: Timer[F]): F[(Marking[Place], Option[EventInstance])] = {
    transition match {
      case interactionTransition: InteractionTransition => executeInteractionInstance(interactionTransition, recipe.petriNet.outMarking(interactionTransition))
      case eventTransition: EventTransition => effect.pure(recipe.petriNet.outMarking(eventTransition).toMarking, input)
      case otherTransition => effect.pure(recipe.petriNet.outMarking(otherTransition).toMarking, None)
    }
  }

  private def executeInteractionInstance[F[_]](interaction: InteractionTransition, outAdjacent: MultiSet[Place])(implicit components: BakerComponents[F], effect: Async[F], timer: Timer[F]): F[(Marking[Place], Option[EventInstance])] = {
    MDC.put("RecipeInstanceId", recipeInstanceId)
    MDC.put("recipeName", recipe.name)

    val execution =
      for {
        timeStarted <- timer.clock.realTime(MILLISECONDS)
        _ <- components.eventStream.publish(InteractionStarted(timeStarted, recipe.name, recipe.recipeId, recipeInstanceId, interaction.interactionName))
        interactionOutput <- components.interactionInstanceManager.execute(interaction, interactionInput(interaction))
        _ <- validateInteractionOutput(interaction, interactionOutput)
        transformedOutput = transformOutputWithTheInteractionTransitionOutputTransformers(interaction, interactionOutput)
        timeCompleted <- timer.clock.realTime(MILLISECONDS)
        _ <- components.eventStream.publish(InteractionCompleted(timeCompleted, timeCompleted - timeStarted, recipe.name, recipe.recipeId, recipeInstanceId, interaction.interactionName, transformedOutput))
        outputMarking = createOutputMarkingForPetriNet(outAdjacent, transformedOutput)
      } yield (outputMarking, transformedOutput)

    execution.handleErrorWith { e =>
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

  private def interactionInput(interaction: InteractionTransition): Seq[IngredientInstance] = {
    // the process id is a special ingredient that is always available
    val recipeInstanceIdIngredient: (String, Value) = il.recipeInstanceIdName -> PrimitiveValue(recipeInstanceId)
    val processIdIngredient: (String, Value) = il.processIdName -> PrimitiveValue(recipeInstanceId)
    // a map of all ingredients
    val allIngredients: Map[String, Value] = ingredients ++ interaction.predefinedParameters + recipeInstanceIdIngredient + processIdIngredient
    // arranges the ingredients in the expected order
    interaction.requiredIngredients.map {
      case IngredientDescriptor(name, _) =>
        IngredientInstance(name, allIngredients.getOrElse(name, throw new FatalInteractionException(s"Missing parameter '$name'")))
    }
  }

  private def exceptionStackTrace(e: Throwable): String = {
    val sw = new StringWriter()
    e.printStackTrace(new PrintWriter(sw))
    sw.toString
  }

  private def handleInteractionInstanceException(throwable: Throwable, failureCount: Int, startTime: Long, outMarking: MultiSet[Place]): FailureStrategy = {
    if (throwable.isInstanceOf[Error])
      BlockTransition
    else
      transition match {
        case interaction: InteractionTransition =>
          // compute the interaction failure strategy outcome
          val failureStrategyOutcome = interaction.failureStrategy.apply(failureCount)
          val currentTime = System.currentTimeMillis()
          //TODO eventStream.publish(InteractionFailed(currentTime, currentTime - startTime, recipe.name, recipe.recipeId, processState.recipeInstanceId, transition.label, failureCount, throwable, failureStrategyOutcome))
          // translates the recipe failure strategy to a petri net failure strategy
          failureStrategyOutcome match {
            case ExceptionStrategyOutcome.BlockTransition => BlockTransition
            case ExceptionStrategyOutcome.RetryWithDelay(delay) => RetryWithDelay(delay)
            case ExceptionStrategyOutcome.Continue(eventName) =>
              val runtimeEvent = EventInstance(eventName, Map.empty)
              Continue(createOutputMarkingForPetriNet(outMarking, Some(runtimeEvent)), Some(runtimeEvent))
          }
        case _ => BlockTransition
      }
  }
}
