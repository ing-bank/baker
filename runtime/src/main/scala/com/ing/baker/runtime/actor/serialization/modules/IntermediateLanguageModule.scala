package com.ing.baker.runtime.actor.serialization.modules

import java.util.concurrent.TimeUnit

import com.ing.baker.il.petrinet.{Node, RecipePetriNet}
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceSerialization.tokenIdentifier
import com.ing.baker.runtime.actor.protobuf
import com.ing.baker.runtime.actor.protobuf._
import com.ing.baker.runtime.actor.serialization.{ProtoEventAdapter, ProtoEventAdapterModule}
import com.ing.baker.types.Value
import com.ing.baker.{il, types}
import scalax.collection.edge.WLDiEdge

import scala.concurrent.duration.Duration

class IntermediateLanguageModule extends ProtoEventAdapterModule {

  implicit class OptionOps[T](option: Option[T]) {
    def getOrMissing(field: String) = option.getOrElse(throw new IllegalStateException(s"missing field: $field"))
  }

  override def toProto(ctx: ProtoEventAdapter): PartialFunction[AnyRef, scalapb.GeneratedMessage] = {
    case il.EventDescriptor(name, ingredients) =>

      val protoIngredients = ingredients.map(ctx.toProto[protobuf.IngredientDescriptor])

      protobuf.EventDescriptor(Some(name), protoIngredients)

    case il.IngredientDescriptor(name, t) =>

      val `type` = ctx.toProto[protobuf.Type](t)

      protobuf.IngredientDescriptor(Some(name), Some(`type`))

    case il.CompiledRecipe(name, recipeId, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod) =>

      val eventReceiveMillis = eventReceivePeriod.map(_.toMillis)
      val retentionMillis = retentionPeriod.map(_.toMillis)

      val nodeList = petriNet.nodes.toList

      val protoNodes: Seq[protobuf.Node] = nodeList.map {

        case Left(il.petrinet.Place(label, placeType)) =>
          val (protoPlaceType, limit) = toProtoPlaceType(placeType)
          val protoPlace = protobuf.Place(Option(label), protoPlaceType, limit)

          protobuf.Node(protobuf.Node.OneofNode.Place(protoPlace))

        case Right(transition) => transition match {

          case il.petrinet.EventTransition(eventDescriptor, isSensoryEvent, maxFiringLimit) =>
            val t = protobuf.EventTransition(Option(ctx.toProto[protobuf.EventDescriptor](eventDescriptor)), Option(isSensoryEvent), maxFiringLimit)
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
              eventsToFire = t.eventsToFire.map(ctx.toProto[protobuf.EventDescriptor]),
              originalEvents = t.originalEvents.map(ctx.toProto[protobuf.EventDescriptor]),
              providedIngredientEvent = None,
              requiredIngredients = t.requiredIngredients.map(ctx.toProto[protobuf.IngredientDescriptor]),
              interactionName = Option(t.interactionName),
              originalInteractionName = Option(t.originalInteractionName),
              predefinedParameters = t.predefinedParameters.mapValues(ctx.toProto[protobuf.Value]),
              maximumInteractionCount = t.maximumInteractionCount,
              failureStrategy = Option(ctx.toProto[protobuf.InteractionFailureStrategy](t.failureStrategy)),
              eventOutputTransformers = t.eventOutputTransformers.mapValues(ctx.toProto[protobuf.EventOutputTransformer])
            )

            protobuf.Node(protobuf.Node.OneofNode.InteractionTransition(pt))

          case t => throw new IllegalStateException(s"Unknown transition type: $t")
        }

        case n => throw new IllegalStateException(s"Unknown node type: $n")
      }

      val protoEdges = petriNet.innerGraph.edges.toList.map { e =>

        val edge = e.label.asInstanceOf[il.petrinet.Edge]
        val from = nodeList.indexOf(e.source.value)
        val to = nodeList.indexOf(e.target.value)

        Edge(Option(from), Option(to), Option(e.weight), edge.eventAllowed)
      }

      val graph: Option[protobuf.PetriNet] = Some(protobuf.PetriNet(protoNodes, protoEdges))

      // from InitialMarking to Seq[ProducedToken]
      val producedTokens: Seq[ProducedToken] = initialMarking.toSeq.flatMap {
        case (place, tokens) ⇒ tokens.toSeq.map {
          case (value, count) ⇒ ProducedToken(
            placeId = Option(place.id),
            tokenId = Option(tokenIdentifier(value)),
            count = Option(count),
            tokenData = Option(ctx.toProtoAny(value.asInstanceOf[AnyRef]))
          )
        }
      }

      protobuf.CompiledRecipe(Option(name), Some(recipeId), graph, producedTokens, validationErrors, eventReceiveMillis, retentionMillis)

    case s: il.failurestrategy.InteractionFailureStrategy => s match {
      case il.failurestrategy.BlockInteraction =>
        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.BlockInteraction(protobuf.BlockInteraction()))
      case il.failurestrategy.FireEventAfterFailure(eventDescriptor) =>
        val fireAfterFailure = protobuf.FireEventAfterFailure(Option(ctx.toProto[protobuf.EventDescriptor](eventDescriptor)))
        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.FireEventAfterFailure(fireAfterFailure))
      case strategy: il.failurestrategy.RetryWithIncrementalBackoff =>
        val retry = protobuf.RetryWithIncrementalBackoff(
          initialTimeout = Option(strategy.initialTimeout.toMillis),
          backoffFactor = Option(strategy.backoffFactor),
          maximumRetries = Option(strategy.maximumRetries),
          maxTimeBetweenRetries = strategy.maxTimeBetweenRetries.map(_.toMillis),
          retryExhaustedEvent = strategy.retryExhaustedEvent.map(ctx.toProto[protobuf.EventDescriptor])
        )

        protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.RetryWithIncrementalBackoff(retry))
    }

    case il.EventOutputTransformer(newEventName, ingredientRenames) =>
      protobuf.EventOutputTransformer(Option(newEventName), ingredientRenames)

  }

  override def toDomain(ctx: ProtoEventAdapter): PartialFunction[scalapb.GeneratedMessage, AnyRef] = {

    case protobuf.PetriNet(protoNodes, protoEdges) =>

      val nodes = protoNodes.map { n =>

        import protobuf.Node.OneofNode

        n.oneofNode match {

          case OneofNode.Place(protobuf.Place(Some(label), Some(placeType), limit)) =>
            val p = il.petrinet.Place(label, toDomainPlaceType(placeType, limit))
            Left(p)

          case OneofNode.EventTransition(protobuf.EventTransition(Some(eventDescriptor), Some(isSensoryEvent), maxFiringLimit)) =>
            Right(il.petrinet.EventTransition(ctx.toDomain[il.EventDescriptor](eventDescriptor), isSensoryEvent, maxFiringLimit))

          case OneofNode.IntermediateTransition(protobuf.IntermediateTransition(Some(label))) =>
            Right(il.petrinet.IntermediateTransition(label))

          case OneofNode.MissingEventTransition(protobuf.MissingEventTransition(Some(label))) =>
            Right(il.petrinet.MissingEventTransition(label))

          case OneofNode.MultiFacilitatorTransition(protobuf.MultiFacilitatorTransition(Some(label))) =>
            Right(il.petrinet.MultiFacilitatorTransition(label))

          case OneofNode.InteractionTransition(t: protobuf.InteractionTransition) =>

            // in 1.3.x an interaction could directly provide an ingredient
            val providedIngredientEvent = t.providedIngredientEvent.map(ctx.toDomain[il.EventDescriptor])

            Right(il.petrinet.InteractionTransition(
              eventsToFire = t.eventsToFire.map(ctx.toDomain[il.EventDescriptor]) ++ providedIngredientEvent,
              originalEvents = t.originalEvents.map(ctx.toDomain[il.EventDescriptor])  ++ providedIngredientEvent,
              requiredIngredients = t.requiredIngredients.map(ctx.toDomain[il.IngredientDescriptor]),
              interactionName = t.interactionName.getOrMissing("interactionName"),
              originalInteractionName = t.originalInteractionName.getOrMissing("originalInteractionName"),
              predefinedParameters = t.predefinedParameters.mapValues(ctx.toDomain[Value]),
              maximumInteractionCount = t.maximumInteractionCount,
              failureStrategy = t.failureStrategy.map(ctx.toDomain[il.failurestrategy.InteractionFailureStrategy]).getOrMissing("failureStrategy"),
              eventOutputTransformers = t.eventOutputTransformers.mapValues(ctx.toDomain[il.EventOutputTransformer])
            ))

          case other => throw new IllegalStateException(s"Unknown node type: $other")
        }
      }

      val params = protoEdges.map {

        case protobuf.Edge(Some(from), Some(to), Some(weight), eventAllowed) =>
          val fromNode = nodes.apply(from.toInt)
          val toNode = nodes.apply(to.toInt)
          val edge = il.petrinet.Edge(eventAllowed)

          WLDiEdge[Any, Any](fromNode, toNode)(weight, edge)
        case other =>
          throw new IllegalArgumentException(s"missing data in: $other")
      }

      scalax.collection.immutable.Graph(params: _*)

    case fs: protobuf.InteractionFailureStrategy => fs.oneofType match {
      case protobuf.InteractionFailureStrategy.OneofType.BlockInteraction(_) =>
        il.failurestrategy.BlockInteraction
      case protobuf.InteractionFailureStrategy.OneofType.FireEventAfterFailure(protobuf.FireEventAfterFailure(Some(event))) =>
        il.failurestrategy.FireEventAfterFailure(ctx.toDomain[il.EventDescriptor](event))
      case protobuf.InteractionFailureStrategy.OneofType.RetryWithIncrementalBackoff(
      protobuf.RetryWithIncrementalBackoff(Some(initialTimeout), Some(backoff), Some(maximumRetries), maxBetween, exhaustedEvent)
      ) =>
        il.failurestrategy.RetryWithIncrementalBackoff(
          initialTimeout = Duration(initialTimeout, TimeUnit.MILLISECONDS),
          backoffFactor = backoff,
          maximumRetries = maximumRetries,
          maxTimeBetweenRetries = maxBetween.map(Duration(_, TimeUnit.MILLISECONDS)),
          retryExhaustedEvent = exhaustedEvent.map(ctx.toDomain[il.EventDescriptor](_)))
      case f => throw new IllegalStateException(s"Unknown failure strategy $f")
    }

    case protobuf.EventDescriptor(Some(name), protoIngredients) =>
      il.EventDescriptor(name, protoIngredients.map(e => ctx.toDomain[il.IngredientDescriptor](e)))

    case protobuf.IngredientDescriptor(Some(name), Some(ingredientType)) =>
      il.IngredientDescriptor(name, ctx.toDomain[types.Type](ingredientType))

    case protobuf.CompiledRecipe(Some(name), optionalRecipeId, Some(graphMsg), producedTokens, validationErrors, eventReceiveMillis, retentionMillis) =>

      val eventReceivePeriod = eventReceiveMillis.map(Duration(_, TimeUnit.MILLISECONDS))
      val retentionPeriod = retentionMillis.map(Duration(_, TimeUnit.MILLISECONDS))

      val graph = ctx.toDomain[scalax.collection.immutable.Graph[Node, WLDiEdge]](graphMsg)
      val petriNet: RecipePetriNet = new com.ing.baker.petrinet.api.PetriNet(graph)
      val initialMarking = producedTokens.foldLeft(Marking.empty[il.petrinet.Place]) {
        case (accumulated, protobuf.ProducedToken(Some(placeId), Some(_), Some(count), _)) ⇒ // Option[SerializedData] is always None, and we don't use it here.
          val place = petriNet.places.getById(placeId, "place in petrinet")
          val value = null // Values are not serialized (not interested in) in the serialized recipe
          accumulated.add(place, value, count)
        case _ ⇒ throw new IllegalStateException("Missing data in persisted ProducedToken")
      }

      optionalRecipeId.map { recipeId =>
        il.CompiledRecipe(name, recipeId, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod)
      }.getOrElse {
        il.CompiledRecipe(name, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod)
      }

    case protobuf.EventOutputTransformer(newEventName, ingredientRenames) =>
      il.EventOutputTransformer(newEventName.getOrMissing("newEventName"), ingredientRenames)

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

  private def toDomainPlaceType(protoPlaceType: protobuf.PlaceType, limit: Option[Int]) = protoPlaceType match {
    case protobuf.PlaceType.IngredientPlace => il.petrinet.Place.IngredientPlace
    case protobuf.PlaceType.InteractionEventOutputPlace => il.petrinet.Place.InteractionEventOutputPlace
    case protobuf.PlaceType.FiringLimiterPlace => il.petrinet.Place.FiringLimiterPlace(limit.getOrMissing("firing limit"))
    case protobuf.PlaceType.EventPreconditionPlace => il.petrinet.Place.EventPreconditionPlace
    case protobuf.PlaceType.EventOrPreconditionPlace => il.petrinet.Place.EventOrPreconditionPlace
    case protobuf.PlaceType.IntermediatePlace => il.petrinet.Place.IntermediatePlace
    case protobuf.PlaceType.EmptyEventIngredientPlace => il.petrinet.Place.EmptyEventIngredientPlace
    case protobuf.PlaceType.MultiTransitionPlace => il.petrinet.Place.MultiTransitionPlace
    case unknownPlaceType => throw new IllegalStateException(s"Unknown protobuf message of type: ${unknownPlaceType.getClass}")
  }
  
}
