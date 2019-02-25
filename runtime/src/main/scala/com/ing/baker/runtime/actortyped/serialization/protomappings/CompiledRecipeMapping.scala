package com.ing.baker.runtime.actortyped.serialization.protomappings

import com.ing.baker.il
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceSerialization.tokenIdentifier
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.ProtobufMapping.{versioned, fromProto => ctxFromProto, toProto => ctxToProto}

import scala.util.{Failure, Success, Try}

class CompiledRecipeMapping(anyMapping: ProtobufMapping.Aux[AnyRef, protobuf.SerializedData]) extends ProtobufMapping[il.CompiledRecipe] {

  type ProtoClass = protobuf.CompiledRecipe

  def toProto(recipe: il.CompiledRecipe): protobuf.CompiledRecipe = {
    val eventReceiveMillis = recipe.eventReceivePeriod.map(_.toMillis)
    val retentionMillis = recipe.retentionPeriod.map(_.toMillis)
    val graph = Some(protobuf.PetriNet(protoNodes(recipe), protoEdges(recipe)))
    protobuf.CompiledRecipe(
      Option(recipe.name),
      Some(recipe.recipeId),
      graph,
      protoMarkings(recipe),
      recipe.validationErrors,
      eventReceiveMillis,
      retentionMillis)
  }

  def fromProto(message: ProtoClass): Try[il.CompiledRecipe] =
    ???

  private def protoNodes(recipe: il.CompiledRecipe): Seq[protobuf.Node] =
    recipe.petriNet.nodes.toList.map {

      case Left(il.petrinet.Place(label, placeType)) =>
        val (protoPlaceType, limit) = toProtoPlaceType(placeType)
        val protoPlace = protobuf.Place(Option(label), protoPlaceType, limit)

        protobuf.Node(protobuf.Node.OneofNode.Place(protoPlace))

      case Right(transition) => transition match {

        case il.petrinet.EventTransition(eventDescriptor, isSensoryEvent, maxFiringLimit) =>
          val t = protobuf.EventTransition(Option(ctxToProto(eventDescriptor)), Option(isSensoryEvent), maxFiringLimit)
          protobuf.Node(protobuf.Node.OneofNode.EventTransition(t))

        case il.petrinet.IntermediateTransition(label) =>
          val t = protobuf.IntermediateTransition(Option(label))
          protobuf.Node(protobuf.Node.OneofNode.IntermediateTransition(t))

        case il.petrinet.MissingEventTransition(label) =>
          val t = protobuf.MissingEventTransition(Option(label))
          protobuf.Node(protobuf.Node.OneofNode.MissingEventTransition(t))

        case il.petrinet.MultiFacilitatorTransition(label) =>
          val t = protobuf.MultiFacilitatorTransition(Option(label))
          protobuf.Node(protobuf.Node.OneofNode.MultiFacilitatorTransition(t))

        case t: il.petrinet.InteractionTransition =>
          val pt = protobuf.InteractionTransition(
            eventsToFire = t.eventsToFire.map(ctxToProto(_)),
            originalEvents = t.originalEvents.map(ctxToProto(_)),
            providedIngredientEvent = None,
            requiredIngredients = t.requiredIngredients.map(ctxToProto(_)),
            interactionName = Option(t.interactionName),
            originalInteractionName = Option(t.originalInteractionName),
            predefinedParameters = t.predefinedParameters.mapValues(ctxToProto(_)),
            maximumInteractionCount = t.maximumInteractionCount,
            failureStrategy = Option(ctxToProto(t.failureStrategy)),
            eventOutputTransformers = t.eventOutputTransformers.mapValues(ctxToProto(_))
          )

          protobuf.Node(protobuf.Node.OneofNode.InteractionTransition(pt))

        case t => throw new IllegalStateException(s"Unknown transition type: $t")
      }

      case n => throw new IllegalStateException(s"Unknown node type: $n")
    }

  private def protoEdges(recipe: il.CompiledRecipe): Seq[protobuf.Edge] = {
    val nodeList = recipe.petriNet.nodes.toList
    val edgeList = recipe.petriNet.innerGraph.edges.toList
    edgeList.map { e =>
      val edge = e.label.asInstanceOf[il.petrinet.Edge]
      val from = nodeList.indexOf(e.source.value)
      val to = nodeList.indexOf(e.target.value)
      protobuf.Edge(Option(from), Option(to), Option(e.weight), edge.eventAllowed)
    }
  }

  private def protoMarkings(recipe: il.CompiledRecipe): Seq[protobuf.ProducedToken] =
    recipe.initialMarking.toSeq.flatMap {
      case (place, tokens) ⇒ tokens.toSeq.map {
        case (value, count) ⇒ protobuf.ProducedToken(
          placeId = Option(place.id),
          tokenId = Option(tokenIdentifier(value)),
          count = Option(count),
          tokenData = Option(anyMapping.toProto(value.asInstanceOf[AnyRef]))
        )
      }
    }

  private def toProtoPlaceType(placeType: il.petrinet.Place.PlaceType): (Option[protobuf.PlaceType], Option[Int]) = placeType match {
    case il.petrinet.Place.IngredientPlace => Option(protobuf.PlaceType.IngredientPlace) -> None
    case il.petrinet.Place.InteractionEventOutputPlace => Option(protobuf.PlaceType.InteractionEventOutputPlace) -> None
    case il.petrinet.Place.FiringLimiterPlace(limit) => Option(protobuf.PlaceType.FiringLimiterPlace) -> Option(limit)
    case il.petrinet.Place.EventPreconditionPlace => Option(protobuf.PlaceType.EventPreconditionPlace) -> None
    case il.petrinet.Place.EventOrPreconditionPlace => Option(protobuf.PlaceType.EventOrPreconditionPlace) -> None
    case il.petrinet.Place.IntermediatePlace => Option(protobuf.PlaceType.IntermediatePlace) -> None
    case il.petrinet.Place.EmptyEventIngredientPlace => Option(protobuf.PlaceType.EmptyEventIngredientPlace) -> None
    case il.petrinet.Place.MultiTransitionPlace => Option(protobuf.PlaceType.MultiTransitionPlace) -> None
  }

  private def toDomainPlaceType(protoPlaceType: protobuf.PlaceType, limit: Option[Int]): Try[il.petrinet.Place.PlaceType] = protoPlaceType match {
    case protobuf.PlaceType.IngredientPlace => Success(il.petrinet.Place.IngredientPlace)
    case protobuf.PlaceType.InteractionEventOutputPlace => Success(il.petrinet.Place.InteractionEventOutputPlace)
    case protobuf.PlaceType.FiringLimiterPlace => versioned(limit, "firingLimit").map(il.petrinet.Place.FiringLimiterPlace)
    case protobuf.PlaceType.EventPreconditionPlace => Success(il.petrinet.Place.EventPreconditionPlace)
    case protobuf.PlaceType.EventOrPreconditionPlace => Success(il.petrinet.Place.EventOrPreconditionPlace)
    case protobuf.PlaceType.IntermediatePlace => Success(il.petrinet.Place.IntermediatePlace)
    case protobuf.PlaceType.EmptyEventIngredientPlace => Success(il.petrinet.Place.EmptyEventIngredientPlace)
    case protobuf.PlaceType.MultiTransitionPlace => Success(il.petrinet.Place.MultiTransitionPlace)
    case unknownPlaceType => Failure(new IllegalStateException(s"Unknown protobuf message of type: ${unknownPlaceType.getClass}"))
  }

}
