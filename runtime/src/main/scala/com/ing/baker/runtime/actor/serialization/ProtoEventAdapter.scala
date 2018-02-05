package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import com.ing.baker.il.petrinet.{Node, RecipePetriNet}
import com.ing.baker.il.{CompiledRecipe, EventDescriptor}
import com.ing.baker.petrinet.api.{IdentifiableOps, Marking, ScalaGraphPetriNet}
import com.ing.baker.runtime.actor.process_index.ProcessIndex
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceSerialization.tokenIdentifier
import com.ing.baker.runtime.actor.protobuf._
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.actor.{process_index, protobuf, recipe_manager}
import com.ing.baker.runtime.core
import com.ing.baker.types.Value
import com.ing.baker.{il, types}
import com.trueaccord.scalapb.GeneratedMessage
import org.joda.time

import scala.concurrent.duration.Duration
import scalax.collection.edge.WLDiEdge

trait ProtoEventAdapter {

  val objectSerializer: ObjectSerializer

  def writeIngredients(ingredients: Seq[(String, Value)]): Seq[protobuf.Ingredient] = {
    ingredients.map { case (name, value) =>
      val serializedObject = objectSerializer.serializeObject(value)
      protobuf.Ingredient(Some(name), Some(serializedObject))
    }
  }

  def readIngredients(ingredients: Seq[protobuf.Ingredient]): Seq[(String, Value)] = {
    ingredients.map {
      case protobuf.Ingredient(Some(name), Some(data)) =>
        val deserializedObject = objectSerializer.deserializeObject(data).asInstanceOf[Value]
        name -> deserializedObject
      case _ => throw new IllegalArgumentException("Missing fields in Protobuf data when deserializing ingredients")
    }
  }

  def toProto(obj: AnyRef): com.trueaccord.scalapb.GeneratedMessage = {

    def createPrimitive(p: PrimitiveType) = protobuf.Type(Type.OneofType.Primitive(p))

    obj match {
      case e: core.RuntimeEvent =>
        val ingredients = writeIngredients(e.providedIngredients)
        protobuf.RuntimeEvent(Some(e.name), ingredients)

      case e: core.ProcessState =>
        val ingredients = writeIngredients(e.ingredients.toSeq)
        protobuf.ProcessState(Some(e.processId), ingredients)

      case il.EventDescriptor(name, ingredients) =>

        val protoIngredients = ingredients.map(i => toProto(i).asInstanceOf[protobuf.IngredientDescriptor])

        protobuf.EventDescriptor(Some(name), protoIngredients)

      case il.IngredientDescriptor(name, t) =>

        val `type` = toProto(t).asInstanceOf[protobuf.Type]

        protobuf.IngredientDescriptor(Some(name), Some(`type`))

      case types.PrimitiveType(clazz) if clazz == classOf[Boolean] =>
        createPrimitive(PrimitiveType.BOOLEAN)
      case types.PrimitiveType(clazz) if clazz == java.lang.Boolean.TYPE =>
        createPrimitive(PrimitiveType.BOOLEAN)
      case types.PrimitiveType(clazz) if clazz == classOf[Byte] =>
        createPrimitive(PrimitiveType.BYTE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Byte.TYPE =>
        createPrimitive(PrimitiveType.BYTE)
      case types.PrimitiveType(clazz) if clazz == classOf[Short] =>
        createPrimitive(PrimitiveType.SHORT)
      case types.PrimitiveType(clazz) if clazz == java.lang.Short.TYPE =>
        createPrimitive(PrimitiveType.SHORT)
      case types.PrimitiveType(clazz) if clazz == classOf[Character] =>
        createPrimitive(PrimitiveType.CHARACTER)
      case types.PrimitiveType(clazz) if clazz == java.lang.Character.TYPE =>
        createPrimitive(PrimitiveType.CHARACTER)
      case types.PrimitiveType(clazz) if clazz == classOf[Integer] =>
        createPrimitive(PrimitiveType.INTEGER)
      case types.PrimitiveType(clazz) if clazz == java.lang.Integer.TYPE =>
        createPrimitive(PrimitiveType.INT)
      case types.PrimitiveType(clazz) if clazz == classOf[Long] =>
        createPrimitive(PrimitiveType.LONG)
      case types.PrimitiveType(clazz) if clazz == java.lang.Long.TYPE =>
        createPrimitive(PrimitiveType.LONG)
      case types.PrimitiveType(clazz) if clazz == classOf[Float] =>
        createPrimitive(PrimitiveType.FLOAT)
      case types.PrimitiveType(clazz) if clazz == java.lang.Float.TYPE =>
        createPrimitive(PrimitiveType.FLOAT)
      case types.PrimitiveType(clazz) if clazz == classOf[Double] =>
        createPrimitive(PrimitiveType.DOUBLE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Double.TYPE =>
        createPrimitive(PrimitiveType.DOUBLE)
      case types.PrimitiveType(clazz) if clazz == classOf[String] =>
        createPrimitive(PrimitiveType.STRING)
      case types.PrimitiveType(clazz) if clazz == classOf[BigDecimal] =>
        createPrimitive(PrimitiveType.BIG_DECIMAL_SCALA)
      case types.PrimitiveType(clazz) if clazz == classOf[java.math.BigDecimal] =>
        createPrimitive(PrimitiveType.BIG_DECIMAL_JAVA)
      case types.PrimitiveType(clazz) if clazz == classOf[BigInt] =>
        createPrimitive(PrimitiveType.BIG_INT_SCALA)
      case types.PrimitiveType(clazz) if clazz == classOf[java.math.BigInteger] =>
        createPrimitive(PrimitiveType.BIG_INT_JAVA)
      case types.PrimitiveType(clazz) if clazz == classOf[Array[Byte]] =>
        createPrimitive(PrimitiveType.BYTE_ARRAY)
      case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.DateTime] =>
        createPrimitive(PrimitiveType.JODA_DATETIME)
      case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.LocalDate] =>
        createPrimitive(PrimitiveType.JODA_LOCAL_DATE)
      case types.PrimitiveType(clazz) if clazz == classOf[org.joda.time.LocalDateTime] =>
        createPrimitive(PrimitiveType.JODA_LOCAL_DATETIME)

      case types.OptionType(entryType) =>
        val entryProto = toProto(entryType).asInstanceOf[protobuf.Type]
        protobuf.Type(Type.OneofType.Optional(OptionalType(Some(entryProto))))

      case types.ListType(entryType) =>
        val entryProto = toProto(entryType).asInstanceOf[protobuf.Type]
        protobuf.Type(Type.OneofType.List(ListType(Some(entryProto))))

      case types.RecordType(fields) =>

        val protoFields = fields.map { f =>
          val protoType = toProto(f.`type`).asInstanceOf[protobuf.Type]
          protobuf.RecordField(Some(f.name), Some(protoType))
        }

        protobuf.Type(Type.OneofType.Record(RecordType(protoFields)))

      case types.MapType(valueType) =>
        val valueProto = toProto(valueType).asInstanceOf[protobuf.Type]
        protobuf.Type(Type.OneofType.Map(MapType(Some(valueProto))))

      case types.EnumType(options) =>
        protobuf.Type(Type.OneofType.Enum(EnumType(options.toSeq)))

      case il.CompiledRecipe(name, petriNet, initialMarking, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod) =>

        val eventReceiveMillis = eventReceivePeriod.map(_.toMillis)
        val retentionMillis = retentionPeriod.map(_.toMillis)
        val sensoryEventsProto = sensoryEvents.map(e => toProto(e).asInstanceOf[protobuf.EventDescriptor]).toSeq

        val nodeList = petriNet.nodes.toList

        val protoNodes = nodeList.map(n => objectSerializer.serializeObject(n)).toSeq
        val protoEdges = petriNet.innerGraph.edges.toList.map{ e =>

          val labelSerializedData = objectSerializer.serializeObject(e.label.asInstanceOf[AnyRef])

//          val protoLabel = toProto(e.label.asInstanceOf[AnyRef]).asInstanceOf[SerializedData]

          val from = nodeList.indexOf(e.source.value)
          val to = nodeList.indexOf(e.target.value)

          Edge(Some(from), Some(to), Some(e.weight), Some(labelSerializedData))
        }

        val graph: Option[protobuf.Graph] = Some(Graph(protoNodes, protoEdges))

        // from InitialMarking to Seq[ProducedToken]
        val producedTokens: Seq[ProducedToken] = initialMarking.data.toSeq.flatMap {
          case (place, tokens) ⇒ tokens.toSeq.map {
            case (value, count) ⇒ ProducedToken(
              placeId = Option(place.id),
              tokenId = Option(tokenIdentifier(place)(value)),
              count = Option(count),
              tokenData = Option(objectSerializer.serializeObject(value.asInstanceOf[AnyRef]))
            )
          }
        }

        protobuf.CompiledRecipe(Some(name), graph, producedTokens, sensoryEventsProto, validationErrors, eventReceiveMillis, retentionMillis)

      case RecipeManager.RecipeAdded(recipeId, compiledRecipe) =>

        val compiledRecipeProto = toProto(compiledRecipe).asInstanceOf[protobuf.CompiledRecipe]

        recipe_manager.protobuf.RecipeAdded(Some(recipeId), Some(compiledRecipeProto))

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

  def toDomain(serializedMessage: GeneratedMessage): AnyRef = {
    serializedMessage match {

      case msg: SerializedData =>

        objectSerializer.deserializeObject(msg)

      case protobuf.RuntimeEvent(Some(name), ingredients) =>
        core.RuntimeEvent(name, readIngredients(ingredients))

      case protobuf.ProcessState(Some(id), ingredients) =>
        core.ProcessState(id, readIngredients(ingredients).toMap)

      case protobuf.Graph(protoNodes, protoEdges) =>

        val nodes = protoNodes.map(n => toDomain(n)).toList

        val params = protoEdges.map {

          case protobuf.Edge(Some(from), Some(to), Some(weight), Some(protoLabel)) =>
          val fromNode = nodes.apply(from.toInt)
          val toNode = nodes.apply(to.toInt)
          val label = toDomain(protoLabel)

          WLDiEdge[Any, Any](fromNode, toNode)(weight, label)
        }

        scalax.collection.immutable.Graph(params: _*)

      case msg: protobuf.Type =>

        msg.`oneofType` match {
          case Type.OneofType.Primitive(PrimitiveType.BOOLEAN) => types.PrimitiveType(classOf[Boolean])
          case Type.OneofType.Primitive(PrimitiveType.BYTE) => types.PrimitiveType(classOf[Byte])
          case Type.OneofType.Primitive(PrimitiveType.SHORT) => types.PrimitiveType(classOf[Short])
          case Type.OneofType.Primitive(PrimitiveType.CHARACTER) => types.PrimitiveType(classOf[Character])
          case Type.OneofType.Primitive(PrimitiveType.INTEGER) => types.PrimitiveType(classOf[Integer])
          case Type.OneofType.Primitive(PrimitiveType.INT) => types.PrimitiveType(classOf[Int])
          case Type.OneofType.Primitive(PrimitiveType.LONG) => types.PrimitiveType(classOf[Long])
          case Type.OneofType.Primitive(PrimitiveType.FLOAT) => types.PrimitiveType(classOf[Float])
          case Type.OneofType.Primitive(PrimitiveType.DOUBLE) => types.PrimitiveType(classOf[Double])
          case Type.OneofType.Primitive(PrimitiveType.STRING) => types.PrimitiveType(classOf[String])
          case Type.OneofType.Primitive(PrimitiveType.BIG_DECIMAL_SCALA) => types.PrimitiveType(classOf[BigDecimal])
          case Type.OneofType.Primitive(PrimitiveType.BIG_DECIMAL_JAVA) => types.PrimitiveType(classOf[java.math.BigDecimal])
          case Type.OneofType.Primitive(PrimitiveType.BIG_INT_SCALA) => types.PrimitiveType(classOf[BigInt])
          case Type.OneofType.Primitive(PrimitiveType.BIG_INT_JAVA) => types.PrimitiveType(classOf[java.math.BigInteger])
          case Type.OneofType.Primitive(PrimitiveType.BYTE_ARRAY) => types.PrimitiveType(classOf[Array[Byte]])
          case Type.OneofType.Primitive(PrimitiveType.JODA_DATETIME) => types.PrimitiveType(classOf[time.DateTime])
          case Type.OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATE) => types.PrimitiveType(classOf[time.LocalDate])
          case Type.OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATETIME) => types.PrimitiveType(classOf[time.LocalDateTime])

          case Type.OneofType.Optional(OptionalType(Some(value))) => types.OptionType(toDomain(value).asInstanceOf[types.Type])

          case Type.OneofType.List(ListType(Some(value))) => types.ListType(toDomain(value).asInstanceOf[types.Type])

          case Type.OneofType.Record(RecordType(fields)) =>
            val mapped = fields.map {
              case protobuf.RecordField(Some(name), Some(fieldType)) =>
                val `type` = toDomain(fieldType).asInstanceOf[types.Type]
                types.RecordField(name, `type`)

              case _ => throw new IllegalStateException(s"Invalid value for record field (properties may not be None)")
            }

            types.RecordType(mapped)

          case Type.OneofType.Map(MapType(Some(value))) => types.MapType(toDomain(value).asInstanceOf[types.Type])

          case Type.OneofType.Enum(EnumType(options)) => types.EnumType(options.toSet).asInstanceOf[types.Type]

          case _ => throw new IllegalStateException(s"Proto message mith missing fields: $msg")
        }

      case protobuf.EventDescriptor(Some(name), protoIngredients) =>
        il.EventDescriptor(name, protoIngredients.map(e => toDomain(e).asInstanceOf[il.IngredientDescriptor]))


      case protobuf.IngredientDescriptor(Some(name), Some(ingredientType)) =>
        il.IngredientDescriptor(name, toDomain(ingredientType).asInstanceOf[types.Type])

      case protobuf.CompiledRecipe(Some(name), Some(graphMsg), producedTokens, protoSensoryEvents, validationErrors, eventReceiveMillis, retentionMillis) =>

        val eventReceivePeriod = eventReceiveMillis.map(Duration(_, TimeUnit.MILLISECONDS))
        val retentionPeriod = retentionMillis.map(Duration(_, TimeUnit.MILLISECONDS))

        val graph = toDomain(graphMsg).asInstanceOf[scalax.collection.immutable.Graph[Node, WLDiEdge]]
        val petriNet: RecipePetriNet = ScalaGraphPetriNet(graph)
        val sensoryEvents = protoSensoryEvents.map(e => toDomain(e).asInstanceOf[EventDescriptor]).toSet
        val initialMarking = producedTokens.foldLeft(Marking.empty[il.petrinet.Place]) {
          case (accumulated, protobuf.ProducedToken(Some(placeId), Some(_), Some(count), _)) ⇒ // Option[SerializedData] is always None, and we don't use it here.
            val place = petriNet.places.getById(placeId, "place in petrinet").asInstanceOf[il.petrinet.Place[Any]]
            val value = null // Values are not serialized (not interested in) in the serialized recipe
            accumulated.add(place, value, count)
          case _ ⇒ throw new IllegalStateException("Missing data in persisted ProducedToken")
        }

        CompiledRecipe(name, petriNet, initialMarking, sensoryEvents, validationErrors, eventReceivePeriod, retentionPeriod)

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

      case _ => throw new IllegalStateException(s"Unkown protobuf message: $serializedMessage")

    }
  }
}
