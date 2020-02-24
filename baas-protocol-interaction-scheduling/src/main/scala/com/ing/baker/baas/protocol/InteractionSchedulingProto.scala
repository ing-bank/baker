package com.ing.baker.baas.protocol

import cats.implicits._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution._
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}

import scala.util.{Success, Try}

object InteractionSchedulingProto {

  implicit def executeInstanceProto: ProtoMap[ExecuteInstance, protobuf.ExecuteInstance] =
    new ProtoMap[ExecuteInstance, protobuf.ExecuteInstance] {

      val companion = protobuf.ExecuteInstance

      def toProto(a: ExecuteInstance): protobuf.ExecuteInstance =
        protobuf.ExecuteInstance(a.input.map(ctxToProto(_)))

      def fromProto(message: protobuf.ExecuteInstance): Try[ExecuteInstance] =
        for {
          result <- message.input.toList.traverse(ctxFromProto(_))
        } yield ExecuteInstance(result)
    }

  implicit def instanceExcutedSuccessfullyProto: ProtoMap[InstanceExecutedSuccessfully, protobuf.InstanceExecutedSuccessfully] =
    new ProtoMap[InstanceExecutedSuccessfully, protobuf.InstanceExecutedSuccessfully] {

      val companion = protobuf.InstanceExecutedSuccessfully

      def toProto(a: InstanceExecutedSuccessfully): protobuf.InstanceExecutedSuccessfully =
        protobuf.InstanceExecutedSuccessfully(a.result.map(ctxToProto(_)))

      def fromProto(message: protobuf.InstanceExecutedSuccessfully): Try[InstanceExecutedSuccessfully] =
        for {
          result <- message.result.traverse(ctxFromProto(_))
        } yield InstanceExecutedSuccessfully(result)
    }

  implicit def instanceExecutionFailedProto: ProtoMap[InstanceExecutionFailed, protobuf.InstanceExecutionFailed] =
    new ProtoMap[InstanceExecutionFailed, protobuf.InstanceExecutionFailed] {

      val companion = protobuf.InstanceExecutionFailed

      def toProto(a: InstanceExecutionFailed): protobuf.InstanceExecutionFailed =
        protobuf.InstanceExecutionFailed(Some(a.message))

      def fromProto(message: protobuf.InstanceExecutionFailed): Try[InstanceExecutionFailed] = {
        for {
          message <- versioned(message.message, "message")
        } yield InstanceExecutionFailed(message)
      }
    }

  implicit def instanceInterfaceProto: ProtoMap[InstanceInterface, protobuf.InstanceInterface] =
    new ProtoMap[InstanceInterface, protobuf.InstanceInterface] {

      val companion = protobuf.InstanceInterface

      def toProto(a: InstanceInterface): protobuf.InstanceInterface =
        protobuf.InstanceInterface(Some(a.name), a.input.map(ctxToProto(_)))

      def fromProto(message: protobuf.InstanceInterface): Try[InstanceInterface] = {
        for {
          name <- versioned(message.name, "name")
          input <- message.input.toList.traverse(ctxFromProto(_))
        } yield InstanceInterface(name, input)
      }
    }

  implicit def instanceExecutionTimedOutProto: ProtoMap[InstanceExecutionTimedOut, protobuf.InstanceExecutionTimedOut] =
    new ProtoMap[InstanceExecutionTimedOut, protobuf.InstanceExecutionTimedOut] {

      val companion = protobuf.InstanceExecutionTimedOut

      def toProto(a: InstanceExecutionTimedOut): protobuf.InstanceExecutionTimedOut =
        protobuf.InstanceExecutionTimedOut()

      def fromProto(message: protobuf.InstanceExecutionTimedOut): Try[InstanceExecutionTimedOut] =
        Success(InstanceExecutionTimedOut())
    }

  implicit def noInstanceFoundProto: ProtoMap[NoInstanceFound.type, protobuf.NoInstanceFound] =
    new ProtoMap[NoInstanceFound.type, protobuf.NoInstanceFound] {

      val companion = protobuf.NoInstanceFound

      def toProto(a: NoInstanceFound.type): protobuf.NoInstanceFound =
        protobuf.NoInstanceFound()

      def fromProto(message: protobuf.NoInstanceFound): Try[NoInstanceFound.type] =
        Success(NoInstanceFound)
    }

  implicit def invalidExecutionProto: ProtoMap[InvalidExecution, protobuf.InvalidExecution] =
    new ProtoMap[InvalidExecution, protobuf.InvalidExecution] {

      val companion = protobuf.InvalidExecution

      def toProto(a: InvalidExecution): protobuf.InvalidExecution =
        protobuf.InvalidExecution()

      def fromProto(message: protobuf.InvalidExecution): Try[InvalidExecution] =
        Success(InvalidExecution())
    }
}
