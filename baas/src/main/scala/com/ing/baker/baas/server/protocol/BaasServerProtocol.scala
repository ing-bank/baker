package com.ing.baker.baas.server.protocol

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent, SensoryEventStatus}
import com.ing.baker.types.{Type, Value}

object BaasServerProtocol {

  sealed trait BaasRequest
  sealed trait BaasResponse

  case class ProcessEventRequest(event: RuntimeEvent) extends BaasRequest
  case class ProcessEventResponse(status: SensoryEventStatus) extends BaasResponse

  case class AddInteractionHTTPRequest(name: String, uri: String, inputTypes: Seq[Type]) extends BaasRequest
  case class AddInteractionHTTPResponse(description: String) extends BaasResponse

  case class BakeRequest(recipeId: String) extends BaasRequest
  case class BakeResponse(processState: ProcessState) extends BaasResponse

  case class AddRecipeRequest(compiledRecipe: CompiledRecipe) extends BaasRequest
  case class AddRecipeResponse(recipeId: String) extends BaasResponse

  case class EventsResponse(events: Seq[RuntimeEvent]) extends BaasResponse

  case class StateResponse(processState: ProcessState) extends BaasResponse

  case class IngredientsResponse(ingredients: Map[String, Value]) extends BaasResponse

  case class VisualStateResponse(visualState: String) extends BaasResponse
}