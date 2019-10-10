package com.ing.baker.runtime.scaladsl

import akka.actor.{ ActorSystem, Address }
import cats.data.NonEmptyList
import com.ing.baker.runtime.akka.{ AkkaBaker, AkkaBakerConfig }
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.common.SensoryEventStatus
import com.typesafe.config.Config
import scala.concurrent.Future

object Baker {

  def akkaLocalDefault(actorSystem: ActorSystem): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.localDefault(actorSystem))

  def akkaClusterDefault(seedNodes: NonEmptyList[Address], actorSystem: ActorSystem): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.clusterDefault(seedNodes, actorSystem))

  def akka(config: AkkaBakerConfig): AkkaBaker =
    new AkkaBaker(config)

  def akka(config: Config, actorSystem: ActorSystem): AkkaBaker =
    new AkkaBaker(AkkaBakerConfig.from(config, actorSystem))

}

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends common.Baker[Future] with ScalaApi {

  override type SensoryEventResultType = SensoryEventResult

  override type EventResolutionsType = EventResolutions

  override type EventInstanceType = EventInstance

  override type RecipeInstanceStateType = RecipeInstanceState

  override type InteractionInstanceType = InteractionInstance

  override type BakerEventType = BakerEvent

  override type RecipeInstanceMetadataType = RecipeInstanceMetadata

  override type RecipeInformationType = RecipeInformation

  override type EventMomentType = EventMoment

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance): Future[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, None)

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String): Future[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, None)

  override def fireEvent(recipeInstanceId: String, event: EventInstance): EventResolutionsType =
    fireEvent(recipeInstanceId, event, None)

  override def fireEventAndResolveWhenReceived(recipeInstanceId: String, event: EventInstance, correlationId: String): Future[SensoryEventStatus] =
    fireEventAndResolveWhenReceived(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveWhenCompleted(recipeInstanceId: String, event: EventInstance, correlationId: String): Future[SensoryEventResultType] =
    fireEventAndResolveWhenCompleted(recipeInstanceId, event, Some(correlationId))

  override def fireEventAndResolveOnEvent(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: String): Future[SensoryEventResult] =
    fireEventAndResolveOnEvent(recipeInstanceId, event, onEvent, Some(correlationId))

  override def fireEvent(recipeInstanceId: String, event: EventInstance, correlationId: String): EventResolutionsType =
    fireEvent(recipeInstanceId, event, Some(correlationId))

}
