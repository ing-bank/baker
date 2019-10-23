package com.ing.baker.runtime.baas

import cats.implicits._
import BaaSProtocol._
import com.ing.baker.runtime.akka.actor.serialization.protomappings.SensoryEventStatusMappingHelper
import com.ing.baker.runtime.akka.actor.serialization.{ProtoMap, SerializersProvider}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap.{ctxFromProto, ctxToProto, versioned}
import scalapb.GeneratedMessageCompanion

import scala.util.Try

object BaaSProto {

  implicit val baaSRemoteFailureProto: ProtoMap[BaaSRemoteFailure, protobuf.BaaSRemoteFailure] =
    new ProtoMap[BaaSRemoteFailure, protobuf.BaaSRemoteFailure] {

      override def companion: GeneratedMessageCompanion[protobuf.BaaSRemoteFailure] =
        protobuf.BaaSRemoteFailure

      override def toProto(a: BaaSRemoteFailure): protobuf.BaaSRemoteFailure =
        protobuf.BaaSRemoteFailure(Some(ctxToProto(a.error)))

      override def fromProto(message: protobuf.BaaSRemoteFailure): Try[BaaSRemoteFailure] =
        versioned(message.failure, "failure")
          .flatMap(ctxFromProto(_))
          .map(BaaSRemoteFailure)
    }

  implicit def addRecipeRequestProto(implicit ev0: SerializersProvider): ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] =
    new ProtoMap[AddRecipeRequest, protobuf.AddRecipeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeRequest] =
        protobuf.AddRecipeRequest

      override def toProto(a: AddRecipeRequest): protobuf.AddRecipeRequest =
        protobuf.AddRecipeRequest(Some(ctxToProto(a.compiledRecipe)))

      override def fromProto(message: protobuf.AddRecipeRequest): Try[AddRecipeRequest] =
        versioned(message.compiledRecipe, "compiledRecipe")
          .flatMap(ctxFromProto(_))
          .map(AddRecipeRequest)
    }

  implicit def addRecipeResponseProto: ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] =
    new ProtoMap[AddRecipeResponse, protobuf.AddRecipeResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.AddRecipeResponse] =
        protobuf.AddRecipeResponse

      override def toProto(a: AddRecipeResponse): protobuf.AddRecipeResponse =
        protobuf.AddRecipeResponse(Some(a.recipeId))

      override def fromProto(message: protobuf.AddRecipeResponse): Try[AddRecipeResponse] =
        versioned(message.recipeId, "recipeId")
          .map(AddRecipeResponse)
    }

  implicit def getRecipeRequestProto: ProtoMap[GetRecipeRequest, protobuf.GetRecipeRequest] =
    new ProtoMap[GetRecipeRequest, protobuf.GetRecipeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.GetRecipeRequest] =
        protobuf.GetRecipeRequest

      override def toProto(a: GetRecipeRequest): protobuf.GetRecipeRequest =
        protobuf.GetRecipeRequest(Some(a.recipeId))

      override def fromProto(message: protobuf.GetRecipeRequest): Try[GetRecipeRequest] =
        versioned(message.recipeId, "recipeId")
          .map(GetRecipeRequest)
    }

  implicit def getRecipeResponseProto(implicit ev0: SerializersProvider): ProtoMap[GetRecipeResponse, protobuf.GetRecipeResponse] =
    new ProtoMap[GetRecipeResponse, protobuf.GetRecipeResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.GetRecipeResponse] =
        protobuf.GetRecipeResponse

      override def toProto(a: GetRecipeResponse): protobuf.GetRecipeResponse =
        protobuf.GetRecipeResponse(Some(ctxToProto(a.recipeInformation)))

      override def fromProto(message: protobuf.GetRecipeResponse): Try[GetRecipeResponse] =
        for {
          recipeInformationProto <- versioned(message.recipeInformation, "recipeInformation")
          recipeInformation <- ctxFromProto(recipeInformationProto)
        } yield GetRecipeResponse(recipeInformation)
    }

  implicit def getAllRecipesResponseProto(implicit ev0: SerializersProvider): ProtoMap[GetAllRecipesResponse, protobuf.GetAllRecipesResponse] =
    new ProtoMap[GetAllRecipesResponse, protobuf.GetAllRecipesResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.GetAllRecipesResponse] =
        protobuf.GetAllRecipesResponse

      override def toProto(a: GetAllRecipesResponse): protobuf.GetAllRecipesResponse =
        protobuf.GetAllRecipesResponse(a.map.mapValues(ctxToProto(_)))

      override def fromProto(message: protobuf.GetAllRecipesResponse): Try[GetAllRecipesResponse] =
        for {
          allRecipes <- message.mapping.toList.traverse { case (id, recipeProto) =>
            ctxFromProto(recipeProto).map(x => (id, x))
          }
        } yield GetAllRecipesResponse(allRecipes.toMap)
    }

  implicit def bakeRequestProto: ProtoMap[BakeRequest, protobuf.BakeRequest] =
    new ProtoMap[BakeRequest, protobuf.BakeRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.BakeRequest] =
        protobuf.BakeRequest

      override def toProto(a: BakeRequest): protobuf.BakeRequest =
        protobuf.BakeRequest(Some(a.recipeId), Some(a.recipeInstanceId))

      override def fromProto(message: protobuf.BakeRequest): Try[BakeRequest] =
        for {
          recipeId <- versioned(message.recipeId, "recipeId")
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        } yield BakeRequest(recipeId, recipeInstanceId)
    }

  implicit def fireEventAndResolveWhenReceivedRequestProto: ProtoMap[FireEventAndResolveWhenReceivedRequest, protobuf.FireEventAndResolveWhenReceivedRequest] =
    new ProtoMap[FireEventAndResolveWhenReceivedRequest, protobuf.FireEventAndResolveWhenReceivedRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveWhenReceivedRequest] =
        protobuf.FireEventAndResolveWhenReceivedRequest

      override def toProto(a: FireEventAndResolveWhenReceivedRequest): protobuf.FireEventAndResolveWhenReceivedRequest =
        protobuf.FireEventAndResolveWhenReceivedRequest(Some(a.recipeInstanceId), Some(ctxToProto(a.event)), a.correlationId)

      override def fromProto(message: protobuf.FireEventAndResolveWhenReceivedRequest): Try[FireEventAndResolveWhenReceivedRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          event <- versioned(message.event, "event")
          decodedEvent <- ctxFromProto(event)
        } yield FireEventAndResolveWhenReceivedRequest(recipeInstanceId, decodedEvent, message.correlationId)
    }

  implicit def fireEventAndResolveWhenReceivedResponseProto: ProtoMap[FireEventAndResolveWhenReceivedResponse, protobuf.FireEventAndResolveWhenReceivedResponse] =
    new ProtoMap[FireEventAndResolveWhenReceivedResponse, protobuf.FireEventAndResolveWhenReceivedResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveWhenReceivedResponse] =
        protobuf.FireEventAndResolveWhenReceivedResponse

      override def toProto(a: FireEventAndResolveWhenReceivedResponse): protobuf.FireEventAndResolveWhenReceivedResponse =
        protobuf.FireEventAndResolveWhenReceivedResponse(Some(SensoryEventStatusMappingHelper.toProto(a.sensoryEventStatus)))

      override def fromProto(message: protobuf.FireEventAndResolveWhenReceivedResponse): Try[FireEventAndResolveWhenReceivedResponse] =
        for {
          sensoryEventStatus <- versioned(message.sensoryEventStatus, "sensoryEventStatus")
          decodedSensoryEventStatus <- SensoryEventStatusMappingHelper.fromProto(sensoryEventStatus)
        } yield FireEventAndResolveWhenReceivedResponse(decodedSensoryEventStatus)
    }

  implicit def fireEventAndResolveWhenCompletedRequestProto: ProtoMap[FireEventAndResolveWhenCompletedRequest, protobuf.FireEventAndResolveWhenCompletedRequest] =
    new ProtoMap[FireEventAndResolveWhenCompletedRequest, protobuf.FireEventAndResolveWhenCompletedRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveWhenCompletedRequest] =
        protobuf.FireEventAndResolveWhenCompletedRequest

      override def toProto(a: FireEventAndResolveWhenCompletedRequest): protobuf.FireEventAndResolveWhenCompletedRequest =
        protobuf.FireEventAndResolveWhenCompletedRequest(Some(a.recipeInstanceId), Some(ctxToProto(a.event)), a.correlationId)

      override def fromProto(message: protobuf.FireEventAndResolveWhenCompletedRequest): Try[FireEventAndResolveWhenCompletedRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          event <- versioned(message.event, "event")
          decodedEvent <- ctxFromProto(event)
        } yield FireEventAndResolveWhenCompletedRequest(recipeInstanceId, decodedEvent, message.correlationId)
    }

  implicit def fireEventAndResolveWhenCompletedResponseProto: ProtoMap[FireEventAndResolveWhenCompletedResponse, protobuf.FireEventAndResolveWhenCompletedResponse] =
    new ProtoMap[FireEventAndResolveWhenCompletedResponse, protobuf.FireEventAndResolveWhenCompletedResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveWhenCompletedResponse] =
        protobuf.FireEventAndResolveWhenCompletedResponse

      override def toProto(a: FireEventAndResolveWhenCompletedResponse): protobuf.FireEventAndResolveWhenCompletedResponse =
        protobuf.FireEventAndResolveWhenCompletedResponse(Some(ctxToProto(a.sensoryEventResult)))

      override def fromProto(message: protobuf.FireEventAndResolveWhenCompletedResponse): Try[FireEventAndResolveWhenCompletedResponse] =
        for {
          sensoryEventResult <- versioned(message.sensoryEventResult, "sensoryEventResult")
          decodedSensoryEventResult <- ctxFromProto(sensoryEventResult)
        } yield FireEventAndResolveWhenCompletedResponse(decodedSensoryEventResult)
    }

  implicit def fireEventAndResolveOnEventRequestProto: ProtoMap[FireEventAndResolveOnEventRequest, protobuf.FireEventAndResolveOnEventRequest] =
    new ProtoMap[FireEventAndResolveOnEventRequest, protobuf.FireEventAndResolveOnEventRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveOnEventRequest] =
        protobuf.FireEventAndResolveOnEventRequest

      override def toProto(a: FireEventAndResolveOnEventRequest): protobuf.FireEventAndResolveOnEventRequest =
        protobuf.FireEventAndResolveOnEventRequest(Some(a.recipeInstanceId), Some(ctxToProto(a.event)), Some(a.onEvent), a.correlationId)

      override def fromProto(message: protobuf.FireEventAndResolveOnEventRequest): Try[FireEventAndResolveOnEventRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          onEvent <- versioned(message.onEvent, "onEvent")
          event <- versioned(message.event, "event")
          decodedEvent <- ctxFromProto(event)
        } yield FireEventAndResolveOnEventRequest(recipeInstanceId, decodedEvent, onEvent, message.correlationId)
    }

  implicit def fireEventAndResolveOnEventResponseProto: ProtoMap[FireEventAndResolveOnEventResponse, protobuf.FireEventAndResolveOnEventResponse] =
    new ProtoMap[FireEventAndResolveOnEventResponse, protobuf.FireEventAndResolveOnEventResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventAndResolveOnEventResponse] =
        protobuf.FireEventAndResolveOnEventResponse

      override def toProto(a: FireEventAndResolveOnEventResponse): protobuf.FireEventAndResolveOnEventResponse =
        protobuf.FireEventAndResolveOnEventResponse(Some(ctxToProto(a.sensoryEventResult)))

      override def fromProto(message: protobuf.FireEventAndResolveOnEventResponse): Try[FireEventAndResolveOnEventResponse] =
        for {
          sensoryEventResult <- versioned(message.sensoryEventResult, "sensoryEventResult")
          decodedSensoryEventResult <- ctxFromProto(sensoryEventResult)
        } yield FireEventAndResolveOnEventResponse(decodedSensoryEventResult)
    }

  implicit def fireEventRequestProto: ProtoMap[FireEventRequest, protobuf.FireEventRequest] =
    new ProtoMap[FireEventRequest, protobuf.FireEventRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.FireEventRequest] =
        protobuf.FireEventRequest

      override def toProto(a: FireEventRequest): protobuf.FireEventRequest =
        protobuf.FireEventRequest(Some(a.recipeInstanceId), Some(ctxToProto(a.event)), a.correlationId)

      override def fromProto(message: protobuf.FireEventRequest): Try[FireEventRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          event <- versioned(message.event, "event")
          decodedEvent <- ctxFromProto(event)
        } yield FireEventRequest(recipeInstanceId, decodedEvent, message.correlationId)
    }

  implicit def getAllRecipeInstancesMetadataResponseProto: ProtoMap[GetAllRecipeInstancesMetadataResponse, protobuf.GetAllRecipeInstancesMetadataResponse] =
    new ProtoMap[GetAllRecipeInstancesMetadataResponse, protobuf.GetAllRecipeInstancesMetadataResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.GetAllRecipeInstancesMetadataResponse] =
        protobuf.GetAllRecipeInstancesMetadataResponse

      override def toProto(a: GetAllRecipeInstancesMetadataResponse): protobuf.GetAllRecipeInstancesMetadataResponse =
        protobuf.GetAllRecipeInstancesMetadataResponse(a.set.toSeq.map(ctxToProto(_)))

      override def fromProto(message: protobuf.GetAllRecipeInstancesMetadataResponse): Try[GetAllRecipeInstancesMetadataResponse] =
        for {
          set <- message.set.toList.traverse(ctxFromProto(_))
        } yield GetAllRecipeInstancesMetadataResponse(set.toSet)
    }

  implicit def getRecipeInstanceStateRequestProto: ProtoMap[GetRecipeInstanceStateRequest, protobuf.GetRecipeInstanceStateRequest] =
    new ProtoMap[GetRecipeInstanceStateRequest, protobuf.GetRecipeInstanceStateRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.GetRecipeInstanceStateRequest] =
        protobuf.GetRecipeInstanceStateRequest

      override def toProto(a: GetRecipeInstanceStateRequest): protobuf.GetRecipeInstanceStateRequest =
        protobuf.GetRecipeInstanceStateRequest(Some(a.recipeInstanceId))

      override def fromProto(message: protobuf.GetRecipeInstanceStateRequest): Try[GetRecipeInstanceStateRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        } yield GetRecipeInstanceStateRequest(recipeInstanceId)
    }

  implicit def getRecipeInstanceStateResponseProto: ProtoMap[GetRecipeInstanceStateResponse, protobuf.GetRecipeInstanceStateResponse] =
    new ProtoMap[GetRecipeInstanceStateResponse, protobuf.GetRecipeInstanceStateResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.GetRecipeInstanceStateResponse] =
        protobuf.GetRecipeInstanceStateResponse

      override def toProto(a: GetRecipeInstanceStateResponse): protobuf.GetRecipeInstanceStateResponse =
        protobuf.GetRecipeInstanceStateResponse(Some(ctxToProto(a.recipeInstanceState)))

      override def fromProto(message: protobuf.GetRecipeInstanceStateResponse): Try[GetRecipeInstanceStateResponse] =
        for {
          recipeInstanceState <- versioned(message.recipeInstanceState, "recipeInstanceState")
          decodedSensoryEventResult <- ctxFromProto(recipeInstanceState)
        } yield GetRecipeInstanceStateResponse(decodedSensoryEventResult)
    }

  implicit def getVisualStateRequestProto: ProtoMap[GetVisualStateRequest, protobuf.GetVisualStateRequest] =
    new ProtoMap[GetVisualStateRequest, protobuf.GetVisualStateRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.GetVisualStateRequest] =
        protobuf.GetVisualStateRequest

      override def toProto(a: GetVisualStateRequest): protobuf.GetVisualStateRequest =
        protobuf.GetVisualStateRequest(Some(a.recipeInstanceId))

      override def fromProto(message: protobuf.GetVisualStateRequest): Try[GetVisualStateRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
        } yield GetVisualStateRequest(recipeInstanceId)
    }

  implicit def getVisualStateResponseProto: ProtoMap[GetVisualStateResponse, protobuf.GetVisualStateResponse] =
    new ProtoMap[GetVisualStateResponse, protobuf.GetVisualStateResponse] {

      override def companion: GeneratedMessageCompanion[protobuf.GetVisualStateResponse] =
        protobuf.GetVisualStateResponse

      override def toProto(a: GetVisualStateResponse): protobuf.GetVisualStateResponse =
        protobuf.GetVisualStateResponse(Some(a.state))

      override def fromProto(message: protobuf.GetVisualStateResponse): Try[GetVisualStateResponse] =
        for {
          state <- versioned(message.state, "state")
        } yield GetVisualStateResponse(state)
    }

  implicit def retryInteractionRequestProto: ProtoMap[RetryInteractionRequest, protobuf.RetryInteractionRequest] =
    new ProtoMap[RetryInteractionRequest, protobuf.RetryInteractionRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.RetryInteractionRequest] =
        protobuf.RetryInteractionRequest

      override def toProto(a: RetryInteractionRequest): protobuf.RetryInteractionRequest =
        protobuf.RetryInteractionRequest(Some(a.recipeInstanceId), Some(a.interactionName))

      override def fromProto(message: protobuf.RetryInteractionRequest): Try[RetryInteractionRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield RetryInteractionRequest(recipeInstanceId, interactionName)
    }

  implicit def resolveInteractionRequestProto: ProtoMap[ResolveInteractionRequest, protobuf.ResolveInteractionRequest] =
    new ProtoMap[ResolveInteractionRequest, protobuf.ResolveInteractionRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.ResolveInteractionRequest] =
        protobuf.ResolveInteractionRequest

      override def toProto(a: ResolveInteractionRequest): protobuf.ResolveInteractionRequest =
        protobuf.ResolveInteractionRequest(Some(a.recipeInstanceId), Some(a.interactionName), Some(ctxToProto(a.event)))

      override def fromProto(message: protobuf.ResolveInteractionRequest): Try[ResolveInteractionRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
          event <- versioned(message.event, "event")
          decodedEvent <- ctxFromProto(event)
        } yield ResolveInteractionRequest(recipeInstanceId, interactionName, decodedEvent)
    }

  implicit def stopRetryingInteractionRequestProto: ProtoMap[StopRetryingInteractionRequest, protobuf.StopRetryingInteractionRequest] =
    new ProtoMap[StopRetryingInteractionRequest, protobuf.StopRetryingInteractionRequest] {

      override def companion: GeneratedMessageCompanion[protobuf.StopRetryingInteractionRequest] =
        protobuf.StopRetryingInteractionRequest

      override def toProto(a: StopRetryingInteractionRequest): protobuf.StopRetryingInteractionRequest =
        protobuf.StopRetryingInteractionRequest(Some(a.recipeInstanceId), Some(a.interactionName))

      override def fromProto(message: protobuf.StopRetryingInteractionRequest): Try[StopRetryingInteractionRequest] =
        for {
          recipeInstanceId <- versioned(message.recipeInstanceId, "recipeInstanceId")
          interactionName <- versioned(message.interactionName, "interactionName")
        } yield StopRetryingInteractionRequest(recipeInstanceId, interactionName)
    }
}
