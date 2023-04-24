package com.ing.baker.runtime.akka.actor.delayed_transition_actor

import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionActor.{DelayedTransitionExecuted, DelayedTransitionInstance, DelayedTransitionScheduled}
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.akka.actor.delayed_transition_actor.DelayedTransitionProto._

import scala.util.Try

object DelayedTransitionProto {

  implicit def delayedTransitionInstanceProto: ProtoMap[DelayedTransitionInstance, protobuf.DelayedTransitionInstance] =
    new ProtoMap[DelayedTransitionInstance, protobuf.DelayedTransitionInstance] {
      val companion = protobuf.DelayedTransitionInstance
      def toProto(a: DelayedTransitionInstance): protobuf.DelayedTransitionInstance = {
        protobuf.DelayedTransitionInstance(
          Some(a.recipeInstanceId),
          Some(a.timeToFire),
          Some(a.jobId),
          Some(a.transitionId),
          Some(a.eventToFire),
          Some(a.fired)
        )
      }

      def fromProto(message: protobuf.DelayedTransitionInstance): Try[DelayedTransitionInstance] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "RecipeInstanceId")
          timeToFire <- versioned(message.timeToFire, "timeToFire")
          jobId <- versioned(message.jobId, "jobId")
          transitionId <- versioned(message.transitionId, "transitionId")
          eventToFire <- versioned(message.eventToFire, "eventToFire")
          fired <- versioned(message.fired, "fired")
        } yield DelayedTransitionInstance(recipeInstanceId, timeToFire, jobId, transitionId, eventToFire, fired, None)
    }

  implicit def delayedTransitionScheduledProto: ProtoMap[DelayedTransitionScheduled, protobuf.DelayedTransitionScheduled] =
    new ProtoMap[DelayedTransitionScheduled, protobuf.DelayedTransitionScheduled] {
      val companion = protobuf.DelayedTransitionScheduled

      def toProto(a: DelayedTransitionScheduled): protobuf.DelayedTransitionScheduled = {
        protobuf.DelayedTransitionScheduled(
          Some(a.id),
          Some(ctxToProto(a.delayedTransitionInstance))
        )
      }

      def fromProto(message: protobuf.DelayedTransitionScheduled): Try[DelayedTransitionScheduled] =
        for {
          id <- versioned(message.id, "id")
          delayedTransitionInstanceProto <- versioned(message. delayedTransitionInstance, " delayedTransitionInstance")
          delayedTransitionInstance <- DelayedTransitionProto.delayedTransitionInstanceProto.fromProto(delayedTransitionInstanceProto)
        } yield DelayedTransitionScheduled(id, delayedTransitionInstance)
    }

  implicit def delayedTransitionExecutedProto: ProtoMap[DelayedTransitionExecuted, protobuf.DelayedTransitionExecuted] =
    new ProtoMap[DelayedTransitionExecuted, protobuf.DelayedTransitionExecuted] {
      val companion = protobuf.DelayedTransitionExecuted

      def toProto(a: DelayedTransitionExecuted): protobuf.DelayedTransitionExecuted = {
        protobuf.DelayedTransitionExecuted(
          Some(a.id),
          Some(ctxToProto(a.delayedTransitionInstance))
        )
      }

      def fromProto(message: protobuf.DelayedTransitionExecuted): Try[DelayedTransitionExecuted] =
        for {
          id <- versioned(message.id, "id")
          delayedTransitionInstanceProto <- versioned(message.delayedTransitionInstance, " delayedTransitionInstance")
          delayedTransitionInstance <- DelayedTransitionProto.delayedTransitionInstanceProto.fromProto(delayedTransitionInstanceProto)
        } yield DelayedTransitionExecuted(id, delayedTransitionInstance)
    }
}
