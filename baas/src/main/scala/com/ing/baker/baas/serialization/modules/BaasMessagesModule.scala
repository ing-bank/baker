package com.ing.baker.baas.serialization.modules

import com.ing.baker.baas.server.protocol
import com.ing.baker.baas.interaction.server.{protocol => interactionProtocol}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.runtime.actor.{protobuf => bakerProto}
import com.ing.baker.runtime.baas.protobuf
import com.ing.baker.runtime.core
import com.ing.baker.types.Value

class BaasMessagesModule extends ProtoEventAdapterModule {

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case protocol.AddInteractionHTTPRequest(name, uri, inputTypes) =>
      val inputTypesProto = inputTypes.map(ctx.toProto[bakerProto.Type])
      protobuf.AddInteractionHTTPRequest(Some(name), Some(uri), inputTypesProto)

    case protocol.AddInteractionHTTPResponse(description) =>
      protobuf.AddInteractionHTTPResponse(Some(description))

    case protocol.AddRecipeRequest(compiledRecipe) =>
      val compiledRecipeProto = ctx.toProto[bakerProto.CompiledRecipe](compiledRecipe)
      protobuf.AddRecipeRequest(Some(compiledRecipeProto))

    case protocol.AddRecipeResponse(recipeId) =>
      protobuf.AddRecipeResponse(Some(recipeId))

    case protocol.BakeRequest(recipeId) =>
      protobuf.BakeRequest(Some(recipeId))

    case protocol.BakeResponse(processState) =>
      val processStateProto = ctx.toProto[bakerProto.ProcessState](processState)
      protobuf.BakeResponse(Some(processStateProto))

    case protocol.EventsResponse(runtimeEvents) =>
      val runtimeEventsProto = runtimeEvents.map(ctx.toProto[bakerProto.RuntimeEvent])
      protobuf.EventsResponse(runtimeEventsProto)

    case protocol.IngredientsResponse(ingredients) =>
      val ingredientsProto = ingredients.map{ case (name, value) => name -> ctx.toProto[bakerProto.Value](value) }
      protobuf.IngredientsResponse(ingredientsProto)

    case protocol.ProcessEventRequest(runtimeEvent) =>
      val runtimeEventProto = ctx.toProto[bakerProto.RuntimeEvent](runtimeEvent)
      protobuf.ProcessEventRequest(Some(runtimeEventProto))

    case protocol.ProcessEventResponse(sensoryEventStatus) =>
      val sensoryEventStatusProto = toSensoryEventStatusProto(sensoryEventStatus)
      protobuf.ProcessEventResponse(Some(sensoryEventStatusProto))

    case protocol.StateResponse(processState) =>
      val processStateProto = ctx.toProto[bakerProto.ProcessState](processState)
      protobuf.StateResponse(Some(processStateProto))

    case protocol.VisualStateResponse(visualState) =>
      protobuf.VisualStateResponse(Some(visualState))

    case interactionProtocol.ExecuteInteractionHTTPRequest(values) =>
      val valuesProto = values.map(ctx.toProto[bakerProto.Value])
      protobuf.ExecuteInteractionHTTPRequest(valuesProto)

    case interactionProtocol.ExecuteInteractionHTTPResponse(runtimeEventOptional) =>
      val runtimeEventOptionalProto =  runtimeEventOptional.map(ctx.toProto[bakerProto.RuntimeEvent])
      protobuf.ExecuteInteractionHTTPResponse(runtimeEventOptionalProto)
  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {
    case protobuf.AddInteractionHTTPRequest(Some(name), Some(uri), inputTypesProto) =>
      val inputTypes = inputTypesProto.map(ctx.toDomain[com.ing.baker.types.Type])
      protocol.AddInteractionHTTPRequest(name, uri, inputTypes)

    case protobuf.AddInteractionHTTPResponse(Some(description)) =>
      protocol.AddInteractionHTTPResponse(description)

    case protobuf.AddRecipeRequest(Some(compiledRecipeProto)) =>
      val compiledRecipe = ctx.toDomain[CompiledRecipe](compiledRecipeProto)
      protocol.AddRecipeRequest(compiledRecipe)

    case protobuf.AddRecipeResponse(Some(recipeId)) =>
      protocol.AddRecipeResponse(recipeId)

    case protobuf.BakeRequest(Some(recipeId)) =>
      protocol.BakeRequest(recipeId)

    case protobuf.BakeResponse(Some(processStateProto)) =>
      val processState = ctx.toDomain[core.ProcessState](processStateProto)
      protocol.BakeResponse(processState)

    case protobuf.EventsResponse(runtimeEventsProto) =>
      val runtimeEvents = runtimeEventsProto.map(ctx.toDomain[core.RuntimeEvent])
      protocol.EventsResponse(runtimeEvents)

    case protobuf.IngredientsResponse(runtimeEventsProto) =>
      val runtimeEvents = runtimeEventsProto.map { case (name, value) => name -> ctx.toDomain[Value](value) }
      protocol.IngredientsResponse(runtimeEvents)

    case protobuf.ProcessEventRequest(Some(runtimeEventProto)) =>
      val runtimeEvent = ctx.toDomain[core.RuntimeEvent](runtimeEventProto)
      protocol.ProcessEventRequest(runtimeEvent)

    case protobuf.ProcessEventResponse(Some(sensoryEventStatus)) =>
      val sensoryEventStatusProto = fromSensoryEventStatusProto(sensoryEventStatus)
      protocol.ProcessEventResponse(sensoryEventStatusProto)

    case protobuf.StateResponse(Some(processStateProto)) =>
      val processState = ctx.toDomain[core.ProcessState](processStateProto)
      protocol.StateResponse(processState)

    case protobuf.VisualStateResponse(Some(visualState)) =>
      protocol.VisualStateResponse(visualState)

    case protobuf.ExecuteInteractionHTTPRequest(valuesProto) =>
      val values = valuesProto.map(ctx.toDomain[Value])
      interactionProtocol.ExecuteInteractionHTTPRequest(values)

    case protobuf.ExecuteInteractionHTTPResponse(runtimeEventOptionalProto) =>
      val runtimeEventOptional = runtimeEventOptionalProto.map(ctx.toDomain[core.RuntimeEvent])
      interactionProtocol.ExecuteInteractionHTTPResponse(runtimeEventOptional)
  }


  def toSensoryEventStatusProto(sensoryEventStatus: core.SensoryEventStatus): protobuf.SensoryEventStatus = {
    sensoryEventStatus match {
      case core.SensoryEventStatus.Received => protobuf.SensoryEventStatus.Received
      case core.SensoryEventStatus.AlreadyReceived => protobuf.SensoryEventStatus.AlreadyReceived
      case core.SensoryEventStatus.Completed => protobuf.SensoryEventStatus.Completed
      case core.SensoryEventStatus.FiringLimitMet => protobuf.SensoryEventStatus.FiringLimitMet
      case core.SensoryEventStatus.ProcessDeleted => protobuf.SensoryEventStatus.ProcessDeleted
      case core.SensoryEventStatus.ReceivePeriodExpired => protobuf.SensoryEventStatus.ReceivePeriodExpired
    }
  }

  def fromSensoryEventStatusProto(sensoryEventStatus: protobuf.SensoryEventStatus): core.SensoryEventStatus = {
    sensoryEventStatus match {
      case protobuf.SensoryEventStatus.Received => core.SensoryEventStatus.Received
      case protobuf.SensoryEventStatus.AlreadyReceived => core.SensoryEventStatus.AlreadyReceived
      case protobuf.SensoryEventStatus.Completed => core.SensoryEventStatus.Completed
      case protobuf.SensoryEventStatus.FiringLimitMet => core.SensoryEventStatus.FiringLimitMet
      case protobuf.SensoryEventStatus.ProcessDeleted => core.SensoryEventStatus.ProcessDeleted
      case protobuf.SensoryEventStatus.ReceivePeriodExpired => core.SensoryEventStatus.ReceivePeriodExpired
      case _ =>  throw new IllegalArgumentException("Invalid SensoryEventStatus received during deserialisation")
    }
  }
}
