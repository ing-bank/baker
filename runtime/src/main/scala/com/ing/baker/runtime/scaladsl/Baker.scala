package com.ing.baker.runtime.scaladsl

import akka.actor.{ActorSystem, Address}
import akka.stream.Materializer
import cats.data.NonEmptyList
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.typesafe.config.Config

import scala.concurrent.Future

object Baker {

  def akkaLocalDefault(actorSystem: ActorSystem, materializer: Materializer): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.localDefault(actorSystem, materializer))

  def akkaClusterDefault(seedNodes: NonEmptyList[Address], actorSystem: ActorSystem, materializer: Materializer): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.clusterDefault(seedNodes, actorSystem, materializer))

  def akka(config: AkkaBakerConfig): AkkaBaker =
    new AkkaBaker(config)

  def akka(config: Config, actorSystem: ActorSystem, materializer: Materializer): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.from(config, actorSystem, materializer))

}

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends common.Baker[Future] with ScalaApi {

  override type EventResultType = EventResult

  override type EventResolutionsType = EventResolutions

  override type RuntimeEventType = EventInstance

  override type ProcessStateType = ProcessState

  override type InteractionImplementationType = InteractionInstance

  override type BakerEventType = BakerEvent

  override type ProcessMetadataType = ProcessMetadata

  override type RecipeInformationType = RecipeInformation

  def fireEventAndResolveWhenReceived(processId: String, event: EventInstance): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(processId, event, None)

  def fireEventAndResolveWhenCompleted(processId: String, event: EventInstance): Future[EventResultType] =
    fireEventAndResolveWhenCompleted(processId, event, None)

  def fireEvent(processId: String, event: EventInstance): EventResolutionsType =
    fireEvent(processId, event, None)

  def fireEventAndResolveWhenReceived(processId: String, event: EventInstance, correlationId: String): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(processId, event, Some(correlationId))

  def fireEventAndResolveWhenCompleted(processId: String, event: EventInstance, correlationId: String): Future[EventResultType] =
    fireEventAndResolveWhenCompleted(processId, event, Some(correlationId))

  def fireEvent(processId: String, event: EventInstance, correlationId: String): EventResolutionsType =
    fireEvent(processId, event, Some(correlationId))

}
