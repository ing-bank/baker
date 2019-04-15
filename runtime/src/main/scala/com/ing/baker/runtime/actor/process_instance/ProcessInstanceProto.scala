package com.ing.baker.runtime.actor.process_instance

import cats.instances.list._
import cats.instances.try_._
import cats.instances.option._
import cats.syntax.traverse._
import com.ing.baker.petrinet.api.{Id, Marking, MultiSet}
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import com.ing.baker.runtime.actortyped.serialization.protomappings.AnyRefMapping.SerializersProvider
import scalapb.GeneratedMessageCompanion

import scala.util.{Failure, Success, Try}

object ProcessInstanceProto {

  implicit def stopProto: ProtoMap[Stop, protobuf.Stop] =
    new ProtoMap[Stop, protobuf.Stop] {

      val companion = protobuf.Stop

      def toProto(a: Stop): protobuf.Stop =
        protobuf.Stop(Some(a.delete))

      def fromProto(message: protobuf.Stop): Try[Stop] =
        for {
          delete <- versioned(message.delete, "delete")
        } yield Stop(delete)
      }

  implicit def getStateProto: ProtoMap[GetState.type , protobuf.GetState] =
    new ProtoMap[GetState.type, protobuf.GetState] {

      val companion = protobuf.GetState

      def toProto(a: GetState.type): protobuf.GetState =
        protobuf.GetState()

      def fromProto(message: protobuf.GetState): Try[GetState.type] =
        Success(GetState)
    }

  implicit def jobStateProto(implicit ev0: SerializersProvider): ProtoMap[JobState, protobuf.JobState] =
    new ProtoMap[JobState, protobuf.JobState] {

      override def companion: GeneratedMessageCompanion[protobuf.JobState] = protobuf.JobState

      override def toProto(a: JobState): protobuf.JobState = ???

      override def fromProto(message: protobuf.JobState): Try[JobState] =
        for {
          jobId <- versioned(message.jobId, "jobid")
          transitionId <- versioned(message.transitionId, "transitionId")
          inputProto <- versioned(message.input, "input")
          consumed <- toDomainMarking(message.consumedMarking)
          input <- ctxFromProto(inputProto)
          exceptionState <- message.exceptionState.traverse[Try, ExceptionState](ctxFromProto(_))
        } yield JobState(jobId, transitionId, consumed, input, exceptionState)

      /*
      case protobuf.JobState(Some(jobId), Some(transitionId), consumed, Some(input), exceptionState) =>
      protocol.JobState(jobId, transitionId, toDomainMarking(consumed, ctx), ctx.toDomain[Any](input), exceptionState.map(ctx.toDomain[protocol.ExceptionState]))
      */
    }

  private def toDomainMarking(markingData: Seq[protobuf.MarkingData])(implicit ev0: SerializersProvider): Try[Marking[Id]] = {
    markingData.foldLeft[Try[Marking[Id]]](Success(Map.empty)) {
      case (accTry, protobuf.MarkingData(Some(placeId), Some(data), Some(count))) =>
        accTry.map { acc =>
          val placeData: MultiSet[Any] = acc.getOrElse(placeId, MultiSet.empty)
          val deserializedData = ctxFromProto(data)
          acc + (placeId -> (placeData + (deserializedData -> count))))
        }
      case _ =>
        Failure(new IllegalStateException("missing data in serialized data when deserializing MarkingData"))
    }
  }

  implicit def instanceStateProto: ProtoMap[InstanceState, protobuf.InstanceState] =
    new ProtoMap[InstanceState, protobuf.InstanceState] {

      val companion = protobuf.InstanceState

      def toProto(a: InstanceState): protobuf.InstanceState =
        protobuf.InstanceState(Some(a.delete))

      def fromProto(message: protobuf.InstanceState): Try[InstanceState] =

      /*
      val jobMap: Map[Long, protocol.JobState] = jobs.map(ctx.toDomain[protocol.JobState]).map(j => j.id -> j).toMap
      protocol.InstanceState(sequenceNr, toDomainMarking(marking, ctx), ctx.toDomain[Any](state), jobMap)
      */

        for {
          jobMap <- message.jobs.toList.traverse[Try, ](ctxToProto(_))
          sequenceNr <- versioned(message.sequenceNr, "sequenceNr")
        } yield InstanceState(delete)
    }
   /*
     Entry("ProcessInstanceProtocol.Stop", classOf[ProcessInstanceProtocol.Stop], actor.process_instance.protobuf.Stop),
     Entry("ProcessInstanceProtocol.GetState", ProcessInstanceProtocol.GetState.getClass, actor.process_instance.protobuf.GetState),
     Entry("ProcessInstanceProtocol.InstanceState", classOf[ProcessInstanceProtocol.InstanceState], actor.process_instance.protobuf.InstanceState),
   */

}
