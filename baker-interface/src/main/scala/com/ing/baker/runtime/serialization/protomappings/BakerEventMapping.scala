package com.ing.baker.runtime.serialization.protomappings

import cats.implicits._
import com.ing.baker.il.failurestrategy.ExceptionStrategyOutcome
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.common.RejectReason
import com.ing.baker.runtime.scaladsl._
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.serialization.protomappings.BakerEventMapping._
import com.ing.baker.runtime.serialization.{ProtoMap, SerializersProvider}
import scalapb.GeneratedMessageCompanion

import scala.util.{Failure, Success, Try}

class BakerEventMapping(implicit ev0: SerializersProvider) extends ProtoMap[BakerEvent, protobuf.BakerEvent] {

  override def companion: GeneratedMessageCompanion[protobuf.BakerEvent] = protobuf.BakerEvent

  override def toProto(a: BakerEvent): protobuf.BakerEvent =
    protobuf.BakerEvent(a match {
      case event: EventReceived => protobuf.BakerEvent.OneofBakerEvent.EventReceived(ctxToProto(event)(EventReceivedMapping))
      case event: EventRejected => protobuf.BakerEvent.OneofBakerEvent.EventRejected(ctxToProto(event)(EventRejectedMapping))
      case event: InteractionCompleted => protobuf.BakerEvent.OneofBakerEvent.InteractionCompleted(ctxToProto(event)(InteractionCompletedMapping))
      case event: InteractionFailed => protobuf.BakerEvent.OneofBakerEvent.InteractionFailed(ctxToProto(event)(InteractionFailedMapping))
      case event: InteractionStarted => protobuf.BakerEvent.OneofBakerEvent.InteractionStarted(ctxToProto(event)(InteractionStartedMapping))
      case event: RecipeInstanceCreated => protobuf.BakerEvent.OneofBakerEvent.RecipeInstanceCreated(ctxToProto(event)(RecipeInstanceCreatedMapping))
      case event: RecipeAdded => protobuf.BakerEvent.OneofBakerEvent.RecipeAdded(ctxToProto(event)(RecipeAddedMapping))
    })

  override def fromProto(message: protobuf.BakerEvent): Try[BakerEvent] =
    message.oneofBakerEvent match {
      case event: protobuf.BakerEvent.OneofBakerEvent.EventReceived => ctxFromProto(event.value)(EventReceivedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.EventRejected=> ctxFromProto(event.value)(EventRejectedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.InteractionCompleted=> ctxFromProto(event.value)(InteractionCompletedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.InteractionFailed => ctxFromProto(event.value)(InteractionFailedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.InteractionStarted => ctxFromProto(event.value)(InteractionStartedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.RecipeInstanceCreated => ctxFromProto(event.value)(RecipeInstanceCreatedMapping)
      case event: protobuf.BakerEvent.OneofBakerEvent.RecipeAdded => ctxFromProto(event.value)(RecipeAddedMapping)
      case protobuf.BakerEvent.OneofBakerEvent.Empty => Failure(new IllegalStateException("Received an Empty protobuf value when trying to deserialize a BakerEvent"))
    }
}

object BakerEventMapping {

  object EventReceivedMapping extends ProtoMap[EventReceived, protobuf.EventReceivedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.EventReceivedBakerEvent] = protobuf.EventReceivedBakerEvent

    override def toProto(a: EventReceived): protobuf.EventReceivedBakerEvent =
      protobuf.EventReceivedBakerEvent(
        timeStamp = Some(a.timeStamp),
        recipeName = Some(a.recipeName),
        recipeId = Some(a.recipeId),
        recipeInstanceId = Some(a.recipeInstanceId),
        correlationId = a.correlationId,
        event = Some(ctxToProto(a.event))
      )

    override def fromProto(message: protobuf.EventReceivedBakerEvent): Try[EventReceived] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        recipeName <- versioned(message.recipeName, "recipeName")
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        correlationId = message.correlationId
        eventProto <- versioned(message.event, "event")
        event <- ctxFromProto(eventProto)
      } yield EventReceived(
        timeStamp = timeStamp,
        recipeName = recipeName,
        recipeId = recipeId,
        recipeInstanceId = recipeInstanceId,
        correlationId = correlationId,
        event = event
      )
  }

  object EventRejectedMapping extends ProtoMap[EventRejected, protobuf.EventRejectedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.EventRejectedBakerEvent] = protobuf.EventRejectedBakerEvent

    override def toProto(a: EventRejected): protobuf.EventRejectedBakerEvent =
      protobuf.EventRejectedBakerEvent(
        timeStamp = Some(a.timeStamp),
        recipeInstanceId = Some(a.recipeInstanceId),
        correlationId = a.correlationId,
        event = Some(ctxToProto(a.event)),
        reason = Some(a.reason match {
          case RejectReason.NoSuchProcess => protobuf.RejectReason.NO_SUCH_PROCESS_REASON
          case RejectReason.ProcessDeleted => protobuf.RejectReason.PROCESS_DELETED_REASON
          case RejectReason.AlreadyReceived => protobuf.RejectReason.ALREADY_RECEIVED_REASON
          case RejectReason.ReceivePeriodExpired => protobuf.RejectReason.RECEIVE_PERIOD_EXPIRED_REASON
          case RejectReason.FiringLimitMet => protobuf.RejectReason.FIRING_LIMIT_MET_REASON
          case RejectReason.InvalidEvent => protobuf.RejectReason.INVALID_EVENT_REASON
        })
      )

    override def fromProto(message: protobuf.EventRejectedBakerEvent): Try[EventRejected] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        correlationId = message.correlationId
        eventProto <- versioned(message.event, "event")
        event <- ctxFromProto(eventProto)
        reason0 <- versioned(message.reason, "reason")
        reason <- reason0 match {
          case protobuf.RejectReason.NO_SUCH_PROCESS_REASON => Success(RejectReason.NoSuchProcess)
          case protobuf.RejectReason.PROCESS_DELETED_REASON => Success(RejectReason.ProcessDeleted)
          case protobuf.RejectReason.ALREADY_RECEIVED_REASON => Success(RejectReason.AlreadyReceived)
          case protobuf.RejectReason.RECEIVE_PERIOD_EXPIRED_REASON => Success(RejectReason.ReceivePeriodExpired)
          case protobuf.RejectReason.FIRING_LIMIT_MET_REASON => Success(RejectReason.FiringLimitMet)
          case protobuf.RejectReason.INVALID_EVENT_REASON => Success(RejectReason.InvalidEvent)
          case protobuf.RejectReason.Unrecognized(int) => Failure(new IllegalStateException(s"Received an Unrecognized($int) protobuf value when trying to deserialize an EventRejected enum."))
        }
      } yield EventRejected(
        timeStamp = timeStamp,
        recipeInstanceId = recipeInstanceId,
        correlationId = correlationId,
        event = event,
        reason = reason
      )
  }

  object InteractionFailedMapping extends ProtoMap[InteractionFailed, protobuf.InteractionFailedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.InteractionFailedBakerEvent] = protobuf.InteractionFailedBakerEvent

    override def toProto(a: InteractionFailed): protobuf.InteractionFailedBakerEvent =
      protobuf.InteractionFailedBakerEvent(
        timeStamp = Some(a.timeStamp),
        duration = Some(a.duration),
        recipeName = Some(a.recipeName),
        recipeId = Some(a.recipeId),
        recipeInstanceId = Some(a.recipeInstanceId),
        interactionName = Some(a.interactionName),
        failureCount = Some(a.failureCount),
        throwable = Some(a.throwable.getMessage + "\n\n" + a.throwable.getStackTrace.toString),
        exceptionStrategyOutcome = Some(a.exceptionStrategyOutcome match {
          case ExceptionStrategyOutcome.BlockTransition => protobuf.ExceptionStrategyOutcome(eventName = None, delay = None)
          case ExceptionStrategyOutcome.Continue(eventName) => protobuf.ExceptionStrategyOutcome(eventName = Some(eventName), delay = None)
          case ExceptionStrategyOutcome.RetryWithDelay(delay) => protobuf.ExceptionStrategyOutcome(eventName = None, delay = Some(delay))
        })
      )

    override def fromProto(message: protobuf.InteractionFailedBakerEvent): Try[InteractionFailed] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        duration <- versioned(message.duration, "duration")
        recipeName <- versioned(message.recipeName, "recipeName")
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        interactionName <- versioned(message.interactionName, "interactionName")
        failureCount <- versioned(message.failureCount, "failureCount")
        throwable <- versioned(message.throwable, "throwable")
        exceptionStrategyOutcome <- versioned(message.exceptionStrategyOutcome, "exceptionStrategyOutcome")
      } yield InteractionFailed(
        timeStamp = timeStamp,
        duration = duration,
        recipeName = recipeName,
        recipeId = recipeId,
        recipeInstanceId = recipeInstanceId,
        interactionName = interactionName,
        failureCount = failureCount,
        throwable = new RuntimeException(throwable),
        exceptionStrategyOutcome = exceptionStrategyOutcome match {
          case protobuf.ExceptionStrategyOutcome(Some(eventName), None) => ExceptionStrategyOutcome.Continue(eventName)
          case protobuf.ExceptionStrategyOutcome(None, Some(delay)) => ExceptionStrategyOutcome.RetryWithDelay(delay)
          case _ => ExceptionStrategyOutcome.BlockTransition
        }
      )
  }

  object InteractionStartedMapping extends ProtoMap[InteractionStarted, protobuf.InteractionStartedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.InteractionStartedBakerEvent] = protobuf.InteractionStartedBakerEvent

    override def toProto(a: InteractionStarted): protobuf.InteractionStartedBakerEvent =
      protobuf.InteractionStartedBakerEvent(
        timeStamp = Some(a.timeStamp),
        recipeName = Some(a.recipeName),
        recipeId = Some(a.recipeId),
        recipeInstanceId = Some(a.recipeInstanceId),
        interactionName = Some(a.interactionName)
      )

    override def fromProto(message: protobuf.InteractionStartedBakerEvent): Try[InteractionStarted] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        recipeName <- versioned(message.recipeName, "recipeName")
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        interactionName <- versioned(message.interactionName, "interactionName")
      } yield InteractionStarted(
        timeStamp = timeStamp,
        recipeName = recipeName,
        recipeId = recipeId,
        recipeInstanceId = recipeInstanceId,
        interactionName = interactionName
      )
  }

  object InteractionCompletedMapping extends ProtoMap[InteractionCompleted, protobuf.InteractionCompletedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.InteractionCompletedBakerEvent] = protobuf.InteractionCompletedBakerEvent

    override def toProto(a: InteractionCompleted): protobuf.InteractionCompletedBakerEvent =
      protobuf.InteractionCompletedBakerEvent(
        timeStamp = Some(a.timeStamp),
        duration = Some(a.duration),
        recipeName = Some(a.recipeName),
        recipeId = Some(a.recipeId),
        recipeInstanceId = Some(a.recipeInstanceId),
        interactionName = Some(a.interactionName),
        event = a.event.map(ctxToProto(_))
      )

    override def fromProto(message: protobuf.InteractionCompletedBakerEvent): Try[InteractionCompleted] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        duration <- versioned(message.duration, "duration")
        recipeName <- versioned(message.recipeName, "recipeName")
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        interactionName <- versioned(message.interactionName, "interactionName")
        event <- message.event.traverse(ctxFromProto(_))
      } yield InteractionCompleted(
        timeStamp = timeStamp,
        duration = duration,
        recipeName = recipeName,
        recipeId = recipeId,
        recipeInstanceId = recipeInstanceId,
        interactionName = interactionName,
        event = event
      )
  }

  object RecipeInstanceCreatedMapping extends ProtoMap[RecipeInstanceCreated, protobuf.RecipeInstanceCreatedBakerEvent] {

    override def companion: GeneratedMessageCompanion[protobuf.RecipeInstanceCreatedBakerEvent] = protobuf.RecipeInstanceCreatedBakerEvent

    override def toProto(a: RecipeInstanceCreated): protobuf.RecipeInstanceCreatedBakerEvent =
      protobuf.RecipeInstanceCreatedBakerEvent(
        timeStamp = Some(a.timeStamp),
        recipeName = Some(a.recipeName),
        recipeId = Some(a.recipeId),
        recipeInstanceId = Some(a.recipeInstanceId)
      )

    override def fromProto(message: protobuf.RecipeInstanceCreatedBakerEvent): Try[RecipeInstanceCreated] =
      for {
        timeStamp <- versioned(message.timeStamp, "timeStamp")
        recipeName <- versioned(message.recipeName, "recipeName")
        recipeId <- versioned(message.recipeId, "recipeId")
        recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
      } yield RecipeInstanceCreated(
        timeStamp = timeStamp,
        recipeName = recipeName,
        recipeId = recipeId,
        recipeInstanceId = recipeInstanceId,
      )
  }

  def RecipeAddedMapping(implicit ev0: SerializersProvider): ProtoMap[RecipeAdded, protobuf.RecipeAddedBakerEvent] =
    new ProtoMap[RecipeAdded, protobuf.RecipeAddedBakerEvent] {

      override def companion: GeneratedMessageCompanion[protobuf.RecipeAddedBakerEvent] = protobuf.RecipeAddedBakerEvent

      override def toProto(a: RecipeAdded): protobuf.RecipeAddedBakerEvent =
        protobuf.RecipeAddedBakerEvent(
          date = Some(a.date),
          recipeName = Some(a.recipeName),
          recipeId = Some(a.recipeId),
          compiledRecipe = Some(ctxToProto(a.compiledRecipe))
        )

      override def fromProto(message: protobuf.RecipeAddedBakerEvent): Try[RecipeAdded] =
        for {
          date <- versioned(message.date, "date")
          recipeName <- versioned(message.recipeName, "recipeName")
          recipeId <- versioned(message.recipeId, "recipeId")
          compiledRecipeProto <- versioned(message.compiledRecipe, "compiledRecipe")
          compiledRecipe <- ctxFromProto(compiledRecipeProto)
        } yield RecipeAdded(
          date = date,
          recipeName = recipeName,
          recipeId = recipeId,
          compiledRecipe = compiledRecipe
        )
    }

}