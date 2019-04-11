package com.ing.baker.runtime.actortyped.serialization.protomappings

import java.util.concurrent.TimeUnit

import cats.syntax.traverse._
import cats.instances.list._
import cats.instances.option._
import cats.instances.try_._
import com.ing.baker.il
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actortyped.serialization.ProtoMap
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceSerialization.tokenIdentifier
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actortyped.serialization.ProtoMap.{versioned, ctxFromProto, ctxToProto}
import com.ing.baker.il.petrinet.{Node, Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api.Marking
import com.ing.baker.types.Value
import scalax.collection.GraphEdge
import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

import scala.concurrent.duration.Duration
import scala.util.{Failure, Success, Try}

class CompiledRecipeMapping(anyMapping: ProtoMap[AnyRef, protobuf.SerializedData]) extends ProtoMap[il.CompiledRecipe, protobuf.CompiledRecipe] {

  val companion = protobuf.CompiledRecipe

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

  def fromProto(message: protobuf.CompiledRecipe): Try[il.CompiledRecipe] = {
    for {
      name <- versioned(message.name, "name")
      graphMsg <- versioned(message.petrinet, "petrinet")
      eventReceivePeriod = message.eventReceivePeriod.map(Duration(_, TimeUnit.MILLISECONDS))
      retentionPeriod = message.retentionPeriod.map(Duration(_, TimeUnit.MILLISECONDS))
      graph <- fromProtoGraph(graphMsg)
      petriNet: RecipePetriNet = new com.ing.baker.petrinet.api.PetriNet(graph)
      initialMarking <- Try(message.initialMarking.foldLeft(Marking.empty[il.petrinet.Place]) {
        case (accumulated, protobuf.ProducedToken(Some(placeId), Some(_), Some(count), _)) ⇒ // Option[SerializedData] is always None, and we don't use it here.
          val place = petriNet.places.getById(placeId, "place in petrinet")
          val value = null // Values are not serialized (not interested in) in the serialized recipe
          accumulated.add(place, value, count)
        case _ ⇒ throw new IllegalStateException("Missing data in persisted ProducedToken")
      })
    } yield message.recipeId.map { recipeId =>
      il.CompiledRecipe(name, recipeId, petriNet, initialMarking, message.validationErrors, eventReceivePeriod, retentionPeriod)
    }.getOrElse {
      il.CompiledRecipe(name, petriNet, initialMarking, message.validationErrors, eventReceivePeriod, retentionPeriod)
    }
  }

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

  def fromProtoGraph(net: protobuf.PetriNet): Try[Graph[Node, WLDiEdge]] = {
    val tryNodes = net.nodes.toList.traverse[Try, Either[Place, Transition]] { n =>

      import protobuf.Node.OneofNode
      n.oneofNode match {

        case place: OneofNode.Place =>
          for {
            label <- versioned(place.value.label, "label")
            placeTypeProto <- versioned(place.value.placeType, "placeType")
            placeType <- toDomainPlaceType(placeTypeProto, place.value.firingLimiterPlaceMaxLimit)
          } yield Left(il.petrinet.Place(label, placeType))

        case transition: OneofNode.EventTransition =>
          for {
            eventDescriptorProto <- versioned(transition.value.eventDescriptor, "eventDescriptor")
            isSensoryEvent <- versioned(transition.value.isSensoryEvent, "isSensoryEvent")
            eventDescriptor <- ctxFromProto(eventDescriptorProto)
            maxFiringLimit = transition.value.maxFiringLimit
          } yield Right(il.petrinet.EventTransition(eventDescriptor, isSensoryEvent, maxFiringLimit))

        case transition: OneofNode.IntermediateTransition =>
          versioned(transition.value.label, "label")
            .map(label => Right(il.petrinet.IntermediateTransition(label)))

        case transition: OneofNode.MissingEventTransition =>
          versioned(transition.value.label, "label")
            .map(label => Right(il.petrinet.MissingEventTransition(label)))

        case transition: OneofNode.MultiFacilitatorTransition =>
          versioned(transition.value.label, "label")
            .map(label => Right(il.petrinet.MultiFacilitatorTransition(label)))

        case transition: OneofNode.InteractionTransition =>
          for {
            // in 1.3.x an interaction could directly provide an ingredient
            providedIngredientEvent <- transition.value
              .providedIngredientEvent
              .traverse(ctxFromProto(_))
            eventDescriptor <- transition.value
              .eventsToFire.toList
              .traverse(ctxFromProto(_))
            originalEvents <- transition.value
              .originalEvents.toList
              .traverse(ctxFromProto(_))
            requiredIngredients <- transition.value
              .requiredIngredients.toList
              .traverse(ctxFromProto(_))
            interactionName <- versioned(transition.value.interactionName, "interactionName")
            originalInteractionName <- versioned(transition.value.originalInteractionName, "originalInteractionName")
            predefinedparameters <- transition.value
              .predefinedParameters.toList
              .traverse[Try, (String, Value)]
                { case (k, v) => ctxFromProto(v).map(k -> _) }
              .map(_.toMap)
            failureStrategyProto <- versioned(transition.value.failureStrategy, "failureStrategy")
            failureStrategy <- ctxFromProto(failureStrategyProto)
            eventOutputTransformers <- transition.value
              .eventOutputTransformers.toList
              .traverse[Try, (String, il.EventOutputTransformer)]
              { case (k, v) => ctxFromProto(v).map(k -> _) }
              .map(_.toMap)
          } yield
            Right(il.petrinet.InteractionTransition(
              eventsToFire = eventDescriptor ++ providedIngredientEvent,
              originalEvents = originalEvents ++ providedIngredientEvent,
              requiredIngredients = requiredIngredients,
              interactionName = interactionName,
              originalInteractionName = originalInteractionName,
              predefinedParameters = predefinedparameters,
              maximumInteractionCount = transition.value.maximumInteractionCount,
              failureStrategy = failureStrategy,
              eventOutputTransformers = eventOutputTransformers
            ))

        case other =>
          // TODO: This is a match over a sealed trait, so in theory the only case in which this would match is when oneOfNode = Empty... should we handle it accordingly?
          Failure(new IllegalStateException(s"Unknown node type: $other"))
      }
    }

    val params = net.edges.toList.traverse[Try, WLDiEdge[Node] with GraphEdge.EdgeCopy[WLDiEdge]] { protoEdge =>
      for {
        from <- versioned(protoEdge.from, "from")
        to <- versioned(protoEdge.to, "to")
        weight <- versioned(protoEdge.weight, "weight")
        fromNode <- tryNodes.map(_.apply(from.toInt))
        toNode <- tryNodes.map(_.apply(to.toInt))
        edge = il.petrinet.Edge(protoEdge.eventFilter)
      } yield WLDiEdge.apply(fromNode, toNode)(weight, edge)
    }

    params.map(p => scalax.collection.immutable.Graph(p: _*))

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
