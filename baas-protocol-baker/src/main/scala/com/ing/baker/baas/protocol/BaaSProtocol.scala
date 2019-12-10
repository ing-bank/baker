package com.ing.baker.baas.protocol

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl._

object BaaSProtocol {

  case class BaaSRemoteFailure(error: BakerException)

  case class AddRecipeRequest(compiledRecipe: CompiledRecipe)

  case class AddRecipeResponse(recipeId: String)

  case class GetRecipeRequest(recipeId: String)

  case class GetRecipeResponse(recipeInformation: RecipeInformation)

  case class GetAllRecipesResponse(map: Map[String, RecipeInformation])

  case class BakeRequest(recipeId: String, recipeInstanceId: String)

  case class FireEventAndResolveWhenReceivedRequest(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])

  case class FireEventAndResolveWhenReceivedResponse(sensoryEventStatus: SensoryEventStatus)

  case class FireEventAndResolveWhenCompletedRequest(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])

  case class FireEventAndResolveWhenCompletedResponse(sensoryEventResult: SensoryEventResult)

  case class FireEventAndResolveOnEventRequest(recipeInstanceId: String, event: EventInstance, onEvent: String, correlationId: Option[String])

  case class FireEventAndResolveOnEventResponse(sensoryEventResult: SensoryEventResult)

  case class FireEventRequest(recipeInstanceId: String, event: EventInstance, correlationId: Option[String])

  // case class FireEventResponse() TODO figure out how to deal with this one

  case class GetAllRecipeInstancesMetadataResponse(set: Set[RecipeInstanceMetadata])

  case class GetRecipeInstanceStateRequest(recipeInstanceId: String)

  case class GetRecipeInstanceStateResponse(recipeInstanceState: RecipeInstanceState)

  case class GetVisualStateRequest(recipeInstanceId: String)

  case class GetVisualStateResponse(state: String)

  case class RetryInteractionRequest(recipeInstanceId: String, interactionName: String)

  case class ResolveInteractionRequest(recipeInstanceId: String, interactionName: String, event: EventInstance)

  case class StopRetryingInteractionRequest(recipeInstanceId: String, interactionName: String)
}
