package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import com.ing.baker.il.{CompiledRecipe, EventType}
import com.ing.baker.il.petrinet.{Node, RecipePetriNet}
import com.ing.baker.petrinet.api.{Marking, ScalaGraphPetriNet}
import com.ing.baker.runtime.actor.messages.SerializedData
import com.ing.baker.runtime.actor.process_index.ProcessIndex
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.{messages, process_index, recipe_manager}
import com.ing.baker.runtime.core
import com.ing.baker.types.Value
import com.trueaccord.scalapb.GeneratedMessage

import scala.concurrent.duration.Duration
import scalax.collection.edge.WLDiEdge

trait DomainProtoTranslation {

  val objectSerializer: ObjectSerializer

  def writeIngredients(ingredients: Seq[(String, Value)]): Seq[messages.Ingredient] = {
    ingredients.map { case (name, value) =>
      val serializedObject = objectSerializer.serializeObject(value)
      messages.Ingredient(Some(name), Some(serializedObject))
    }
  }

  def readIngredients(ingredients: Seq[messages.Ingredient]): Seq[(String, Value)] = {
    ingredients.map {
      case messages.Ingredient(Some(name), Some(data)) =>
        val deserializedObject = objectSerializer.deserializeObject(data).asInstanceOf[Value]
        name -> deserializedObject
      case _ => throw new IllegalArgumentException("Missing fields in Protobuf data when deserializing ingredients")
    }
  }

  def toProto(obj: AnyRef): com.trueaccord.scalapb.GeneratedMessage = {

    obj match {
      case e: core.RuntimeEvent =>
        val ingredients = writeIngredients(e.providedIngredients)
        messages.RuntimeEvent(Some(e.name), ingredients)

      case e: core.ProcessState =>
        val ingredients = writeIngredients(e.ingredients.toSeq)
        messages.ProcessState(Some(e.processId), ingredients)

      case CompiledRecipe(name, petriNet, initialMarking, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod) =>

        val eventReceiveMillis = eventReceivePeriod.map(_.toMillis)
        val retentionMillis = retentionPeriod.map(_.toMillis)
        val sensoryEventMsg = sensoryEvents.map(e => toProto(obj).asInstanceOf[messages.EventType]).toSeq
        val graph: Option[messages.Graph] = None

        messages.CompiledRecipe(Some(name), graph, sensoryEventMsg, validationErrors, eventReceiveMillis, retentionMillis)

      case ProcessIndex.ActorCreated(recipeId, processId, createdDateTime) =>

        process_index.protobuf.ActorCreated(Some(recipeId), Some(processId), Some(createdDateTime))
      case ProcessIndex.ActorPassivated(processId) =>
        process_index.protobuf.ActorPassivated(Some(processId))
      case ProcessIndex.ActorActivated(processId) =>
        process_index.protobuf.ActorActivated(Some(processId))
      case ProcessIndex.ActorDeleted(processId) =>
        process_index.protobuf.ActorDeleted(Some(processId))
    }
  }

  def toDomain(protobuf: GeneratedMessage): AnyRef = {
    protobuf match {

      case msg: SerializedData =>

        objectSerializer.deserializeObject(msg)

      case messages.RuntimeEvent(Some(name), ingredients) =>
        core.RuntimeEvent(name, readIngredients(ingredients))

      case messages.ProcessState(Some(id), ingredients) =>
        core.ProcessState(id, readIngredients(ingredients).toMap)

      case messages.Graph(nodes, edges) =>

        val params = edges.map {

          case messages.Edge(Some(from), Some(to), Some(weight), Some(labelMsg)) =>
          val fromNode = toDomain(nodes.apply(from.toInt))
          val toNode = toDomain(nodes.apply(to.toInt))
          val label = toDomain(labelMsg)

          WLDiEdge[Any, Any](fromNode, toNode)(weight, label)
        }

        scalax.collection.immutable.Graph(params: _*)


      case messages.EventType(Some(name), Some(eventType)) =>
        EventType(name, null)

      case messages.CompiledRecipe(Some(name), Some(graphMsg), sensoryEventMsg, validationErrors, eventReceiveMillis, retentionMillis) =>

        val eventReceivePeriod = eventReceiveMillis.map(Duration(_, TimeUnit.MILLISECONDS))
        val retentionPeriod = retentionMillis.map(Duration(_, TimeUnit.MILLISECONDS))

        val graph = toDomain(graphMsg).asInstanceOf[scalax.collection.immutable.Graph[Node, WLDiEdge]]
        val petriNet: RecipePetriNet = ScalaGraphPetriNet(graph)
        val sensoryEvents = sensoryEventMsg.map(e => toDomain(e).asInstanceOf[EventType]).toSet

        CompiledRecipe(name, petriNet, Marking.empty, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod)

      case recipe_manager.protobuf.RecipeAdded(Some(recipeId), (Some(compiledRecipeMsg))) =>

        val compiledRecipe = toDomain(compiledRecipeMsg).asInstanceOf[CompiledRecipe]
        RecipeAdded(recipeId, compiledRecipe)

      case process_index.protobuf.ActorCreated(Some(recipeId), Some(processId), Some(dateCreated)) =>
        ProcessIndex.ActorCreated(recipeId, processId, dateCreated)

      case process_index.protobuf.ActorPassivated(Some(processId)) =>
        ProcessIndex.ActorPassivated(processId)

      case process_index.protobuf.ActorActivated(Some(processId)) =>
        ProcessIndex.ActorActivated(processId)

      case process_index.protobuf.ActorDeleted(Some(processId)) =>
        ProcessIndex.ActorDeleted(processId)

      case _ => throw new IllegalStateException(s"Unkown protobuf message: $protobuf")

    }
  }
}
