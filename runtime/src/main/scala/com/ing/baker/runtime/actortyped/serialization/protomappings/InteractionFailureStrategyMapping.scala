package com.ing.baker.runtime.actortyped.serialization.protomappings

import java.util.concurrent.TimeUnit

import cats.implicits._
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.il
import com.ing.baker.il.failurestrategy.InteractionFailureStrategy
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}

import scala.util.{Failure, Success, Try}
import scala.concurrent.duration._

class InteractionFailureStrategyMapping extends ProtoMap[il.failurestrategy.InteractionFailureStrategy, protobuf.InteractionFailureStrategy] {

  val companion = protobuf.InteractionFailureStrategy

  override def toProto(strategy: InteractionFailureStrategy): protobuf.InteractionFailureStrategy =
    strategy match {

      case il.failurestrategy.BlockInteraction =>
        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.BlockInteraction(protobuf.BlockInteraction()))

      case il.failurestrategy.FireEventAfterFailure(eventDescriptor) =>
        val fireAfterFailure =
          protobuf.FireEventAfterFailure(Option(ctxToProto(eventDescriptor)))
        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.FireEventAfterFailure(fireAfterFailure))

      case strategy: il.failurestrategy.RetryWithIncrementalBackoff =>
        val retry = protobuf.RetryWithIncrementalBackoff(
          initialTimeout = Option(strategy.initialTimeout.toMillis),
          backoffFactor = Option(strategy.backoffFactor),
          maximumRetries = Option(strategy.maximumRetries),
          maxTimeBetweenRetries = strategy.maxTimeBetweenRetries.map(_.toMillis),
          retryExhaustedEvent = strategy.retryExhaustedEvent.map(ctxToProto(_))
        )

        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.RetryWithIncrementalBackoff(retry))
    }

  override def fromProto(message: protobuf.InteractionFailureStrategy): Try[InteractionFailureStrategy] = {
    import protobuf.InteractionFailureStrategy.OneofType
    message.oneofType match {

      case OneofType.BlockInteraction(_) =>
        Success(il.failurestrategy.BlockInteraction)

      case OneofType.FireEventAfterFailure(fireEvent: protobuf.FireEventAfterFailure) =>
        for {
          eventProto <- versioned(fireEvent.event, "event")
          event <- ctxFromProto(eventProto)
        } yield il.failurestrategy.FireEventAfterFailure(event)

      case OneofType.RetryWithIncrementalBackoff(incremental: protobuf.RetryWithIncrementalBackoff) =>
        for {
          initialTimeout <- versioned(incremental.initialTimeout, "initialTimeout")
          backoff <- versioned(incremental.backoffFactor, "backoffFactor")
          maximumRetries <- versioned(incremental.maximumRetries, "maximumRetries")
          retryExausted <- incremental.retryExhaustedEvent.traverse[Try, il.EventDescriptor](ctxFromProto(_))
        } yield il.failurestrategy.RetryWithIncrementalBackoff(
          initialTimeout = Duration(initialTimeout, TimeUnit.MILLISECONDS),
          backoffFactor = backoff,
          maximumRetries = maximumRetries,
          maxTimeBetweenRetries = incremental.maxTimeBetweenRetries.map(Duration(_, TimeUnit.MILLISECONDS)),
          retryExhaustedEvent = retryExausted
        )

      case f =>
        Failure(new IllegalStateException(s"Unknown failure strategy $f"))
    }
  }
}
