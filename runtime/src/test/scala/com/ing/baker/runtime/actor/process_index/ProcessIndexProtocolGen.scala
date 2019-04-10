package com.ing.baker.runtime.actor.process_index

import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndex._
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._
import com.ing.baker.runtime.core.RuntimeEventGen
import org.scalacheck.Gen

import scala.concurrent.duration._

object ProcessIndexProtocolGen {

  def identifierGen: Gen[String] = Gen.alphaNumStr

  def timestampGen: Gen[Long] = Gen.chooseNum(100000l, 1000000l)

  def getShardIndex: Gen[GetShardIndex] =
    identifierGen.map(GetShardIndex)

  def actorCreated: Gen[ActorCreated] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
      timestamp <- timestampGen
    } yield ActorCreated(recipeId, processId, timestamp)

  def actorActivated: Gen[ActorActivated] =
    identifierGen.map(ActorActivated)

  def actorPassivated: Gen[ActorPassivated] =
    identifierGen.map(ActorPassivated)

  def actorDeleted: Gen[ActorDeleted] =
    identifierGen.map(ActorDeleted)

  def actorMetadata: Gen[ActorMetadata] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
      timestamp <- timestampGen
      status <- Gen.oneOf(ProcessIndex.Active, ProcessIndex.Deleted)
    } yield ActorMetadata(recipeId, processId, timestamp, status)

  def index: Gen[Index] =
    for {
      metadata <- Gen.listOf(actorMetadata)
    } yield Index(metadata)

  def createProcess: Gen[CreateProcess] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
    } yield CreateProcess(recipeId, processId)

  def processEvent: Gen[ProcessEvent] =
    for {
      processId <- identifierGen
      event <- RuntimeEventGen.gen
    } yield ProcessEvent(processId, event, None, false, 100.millis)

  def retryBlockedInteraction: Gen[RetryBlockedInteraction] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
    } yield RetryBlockedInteraction(recipeId, processId)

  def resolveBlockedInteraction: Gen[ResolveBlockedInteraction] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
      event <- RuntimeEventGen.gen
    } yield ResolveBlockedInteraction(recipeId, processId, event)

  def stopRetryingInteraction: Gen[StopRetryingInteraction] =
    for {
      recipeId <- identifierGen
      processId <- identifierGen
    } yield StopRetryingInteraction(recipeId, processId)

}
