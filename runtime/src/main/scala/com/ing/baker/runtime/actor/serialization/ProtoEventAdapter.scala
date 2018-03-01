package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import com.google.protobuf.ByteString
import com.ing.baker.il.ActionType.SieveAction
import com.ing.baker.il.petrinet.{Node, RecipePetriNet}
import com.ing.baker.il.{ActionType, CompiledRecipe}
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
import org.joda.time.{LocalDate, LocalDateTime}
import org.joda.time.format.ISODateTimeFormat

import scala.concurrent.duration.Duration
import scalax.collection.edge.WLDiEdge

trait ProtoEventAdapter {

  implicit class OptionOps[T](option: Option[T]) {
    def getOrMissing(field: String) = option.getOrElse(throw new IllegalStateException(s"missing field: $field"))
  }

  implicit class MsgOptionOps[T <: GeneratedMessage](option: Option[T]) {
    def mapToDomain[B]: Option[B] = option.map(e => toDomainType[B](e))
  }

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

  def toProtoType[T <: GeneratedMessage](obj: AnyRef): T = toProto(obj).asInstanceOf[T]

  def toProto(obj: AnyRef): com.trueaccord.scalapb.GeneratedMessage = {

    def createPrimitive(p: PrimitiveType) = protobuf.Type(Type.OneofType.Primitive(p))

    obj match {
      case e: core.RuntimeEvent =>
        val ingredients = writeIngredients(e.providedIngredients)
        protobuf.RuntimeEvent(Some(e.name), ingredients)

      case e: core.ProcessState =>
        val ingredients = writeIngredients(e.ingredients.toSeq)
        protobuf.ProcessState(Some(e.processId), ingredients, e.eventNames)

      case il.EventDescriptor(name, ingredients) =>

        val protoIngredients = ingredients.map(toProtoType[protobuf.IngredientDescriptor])

        protobuf.EventDescriptor(Some(name), protoIngredients)

      case il.IngredientDescriptor(name, t) =>

        val `type` = toProtoType[protobuf.Type](t)

        protobuf.IngredientDescriptor(Some(name), Some(`type`))

      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Boolean] =>
        createPrimitive(PrimitiveType.BOOLEAN_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Boolean.TYPE =>
        createPrimitive(PrimitiveType.BOOLEAN)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Byte] =>
        createPrimitive(PrimitiveType.BYTE_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Byte.TYPE =>
        createPrimitive(PrimitiveType.BYTE)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Short] =>
        createPrimitive(PrimitiveType.SHORT_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Short.TYPE =>
        createPrimitive(PrimitiveType.SHORT)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Character] =>
        createPrimitive(PrimitiveType.CHARACTER_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Character.TYPE =>
        createPrimitive(PrimitiveType.CHARACTER)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Integer] =>
        createPrimitive(PrimitiveType.INTEGER)
      case types.PrimitiveType(clazz) if clazz == java.lang.Integer.TYPE =>
        createPrimitive(PrimitiveType.INT)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Long] =>
        createPrimitive(PrimitiveType.LONG_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Long.TYPE =>
        createPrimitive(PrimitiveType.LONG)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Float] =>
        createPrimitive(PrimitiveType.FLOAT_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Float.TYPE =>
        createPrimitive(PrimitiveType.FLOAT)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.Double] =>
        createPrimitive(PrimitiveType.DOUBLE_PRIMITIVE)
      case types.PrimitiveType(clazz) if clazz == java.lang.Double.TYPE =>
        createPrimitive(PrimitiveType.DOUBLE)
      case types.PrimitiveType(clazz) if clazz == classOf[java.lang.String] =>
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
        val entryProto = toProtoType[protobuf.Type](entryType)
        protobuf.Type(Type.OneofType.Optional(OptionalType(Some(entryProto))))

      case types.ListType(entryType) =>
        val entryProto = toProtoType[protobuf.Type](entryType)
        protobuf.Type(Type.OneofType.List(ListType(Some(entryProto))))

      case types.RecordType(fields) =>

        val protoFields = fields.map { f =>
          val protoType = toProtoType[protobuf.Type](f.`type`)
          protobuf.RecordField(Some(f.name), Some(protoType))
        }

        protobuf.Type(Type.OneofType.Record(RecordType(protoFields)))

      case types.MapType(valueType) =>
        val valueProto = toProtoType[protobuf.Type](valueType)
        protobuf.Type(Type.OneofType.Map(MapType(Some(valueProto))))

      case types.EnumType(options) =>
        protobuf.Type(Type.OneofType.Enum(EnumType(options.toSeq)))

      case il.CompiledRecipe(name, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod) =>

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
              val t = protobuf.EventTransition(Option(toProto(eventDescriptor).asInstanceOf[protobuf.EventDescriptor]), Option(isSensoryEvent), maxFiringLimit)
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

            case t: il.petrinet.InteractionTransition[_] =>
              val pt = protobuf.InteractionTransition(
                eventsToFire = t.eventsToFire.map(toProtoType[protobuf.EventDescriptor]),
                originalEvents = t.originalEvents.map(toProtoType[protobuf.EventDescriptor]),
                providedIngredientEvent = t.providedIngredientEvent.map(toProtoType[protobuf.EventDescriptor]),
                requiredIngredients = t.requiredIngredients.map(toProtoType[protobuf.IngredientDescriptor]),
                interactionName = Option(t.interactionName),
                originalInteractionName = Option(t.originalInteractionName),
                isSieve = Option(t.actionType.equals(SieveAction)),
                predefinedParameters = t.predefinedParameters.mapValues(toProtoType[protobuf.Value]),
                maximumInteractionCount = t.maximumInteractionCount,
                failureStrategy = Option(toProtoType[protobuf.InteractionFailureStrategy](t.failureStrategy)),
                eventOutputTransformers = t.eventOutputTransformers.mapValues(toProtoType[protobuf.EventOutputTransformer])
              )

              protobuf.Node(protobuf.Node.OneofNode.InteractionTransition(pt))

            case t => throw new IllegalStateException(s"Unkown transition type: $t")
          }

          case n => throw new IllegalStateException(s"Unkown node type: $n")
        }

        val protoEdges = petriNet.innerGraph.edges.toList.map{ e =>

          val edge = e.label.asInstanceOf[il.petrinet.Edge[_]]
          val from = nodeList.indexOf(e.source.value)
          val to = nodeList.indexOf(e.target.value)

          Edge(Option(from), Option(to), Option(e.weight), edge.eventAllowed)
        }

        val graph: Option[protobuf.PetriNet] = Some(protobuf.PetriNet(protoNodes, protoEdges))

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

        protobuf.CompiledRecipe(Option(name), graph, producedTokens, validationErrors, eventReceiveMillis, retentionMillis)

      case RecipeManager.RecipeAdded(recipeId, compiledRecipe) =>
        val compiledRecipeProto = toProto(compiledRecipe).asInstanceOf[protobuf.CompiledRecipe]
        recipe_manager.protobuf.RecipeAdded(Option(recipeId), Option(compiledRecipeProto))

      case ProcessIndex.ActorCreated(recipeId, processId, createdDateTime) =>
        process_index.protobuf.ActorCreated(Option(recipeId), Option(processId), Option(createdDateTime))

      case ProcessIndex.ActorPassivated(processId) =>
        process_index.protobuf.ActorPassivated(Option(processId))

      case ProcessIndex.ActorActivated(processId) =>
        process_index.protobuf.ActorActivated(Option(processId))

      case ProcessIndex.ActorDeleted(processId) =>
        process_index.protobuf.ActorDeleted(Option(processId))

      case s: il.failurestrategy.InteractionFailureStrategy => s match {
        case il.failurestrategy.BlockInteraction =>
          protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.BlockInteraction(protobuf.BlockInteraction()))
        case il.failurestrategy.FireEventAfterFailure(eventDescriptor) =>
          val fireAfterFailure = protobuf.FireEventAfterFailure(Option(toProto(eventDescriptor).asInstanceOf[protobuf.EventDescriptor]))
          protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.FireEventAfterFailure(fireAfterFailure))
        case strategy: il.failurestrategy.RetryWithIncrementalBackoff =>
          val retry = protobuf.RetryWithIncrementalBackoff(
            initialTimeout = Option(strategy.initialTimeout.toMillis),
            backoffFactor = Option(strategy.backoffFactor),
            maximumRetries = Option(strategy.maximumRetries),
            maxTimeBetweenRetries = strategy.maxTimeBetweenRetries.map(_.toMillis),
            retryExhaustedEvent = strategy.retryExhaustedEvent.map(toProtoType[protobuf.EventDescriptor])
          )

          protobuf.InteractionFailureStrategy(protobuf.InteractionFailureStrategy.OneofType.RetryWithIncrementalBackoff(retry))
      }

      case il.EventOutputTransformer(newEventName, ingredientRenames) =>
        protobuf.EventOutputTransformer(Option(newEventName), ingredientRenames)

      case v: types.Value => v match {
        case types.NullValue => protobuf.Value(protobuf.Value.OneofValue.NullValue(true))
        case types.PrimitiveValue(value: Boolean) => protobuf.Value(protobuf.Value.OneofValue.BooleanValue(value))
        case types.PrimitiveValue(value: Byte) => protobuf.Value(protobuf.Value.OneofValue.ByteValue(value))
        case types.PrimitiveValue(value: Short) => protobuf.Value(protobuf.Value.OneofValue.ShortValue(value))
        case types.PrimitiveValue(value: Char) => protobuf.Value(protobuf.Value.OneofValue.CharValue(value))
        case types.PrimitiveValue(value: Int) => protobuf.Value(protobuf.Value.OneofValue.IntValue(value))
        case types.PrimitiveValue(value: Long) => protobuf.Value(protobuf.Value.OneofValue.LongValue(value))
        case types.PrimitiveValue(value: Float) => protobuf.Value(protobuf.Value.OneofValue.FloatValue(value))
        case types.PrimitiveValue(value: Double) => protobuf.Value(protobuf.Value.OneofValue.DoubleValue(value))
        case types.PrimitiveValue(value: String) => protobuf.Value(protobuf.Value.OneofValue.StringValue(value))
        case types.PrimitiveValue(value: BigDecimal) => protobuf.Value(protobuf.Value.OneofValue.BigDecimalScalaValue(value.toString()))
        case types.PrimitiveValue(value: java.math.BigDecimal) => protobuf.Value(protobuf.Value.OneofValue.BigDecimalJavaValue(BigDecimal(value).toString()))
        case types.PrimitiveValue(value: BigInt) => protobuf.Value(protobuf.Value.OneofValue.BigIntScalaValue(value.toString()))
        case types.PrimitiveValue(value: java.math.BigInteger) => protobuf.Value(protobuf.Value.OneofValue.BigIntJavaValue(BigInt(value).toString()))
        case types.PrimitiveValue(value: Array[Byte]) => protobuf.Value(protobuf.Value.OneofValue.ByteArrayValue(ByteString.copyFrom(value)))
        case types.PrimitiveValue(value: org.joda.time.DateTime) => protobuf.Value(protobuf.Value.OneofValue.JodaDatetimeValue(ISODateTimeFormat.dateTime().print(value)))
        case types.PrimitiveValue(value: org.joda.time.LocalDate) => protobuf.Value(protobuf.Value.OneofValue.JodaLocaldateValue(value.toString))
        case types.PrimitiveValue(value: org.joda.time.LocalDateTime) => protobuf.Value(protobuf.Value.OneofValue.JodaLocaldatetimeValue(value.toString))
        case types.PrimitiveValue(value) => throw new IllegalStateException(s"Unknown primitive value: $value")
        case types.RecordValue(entries) => protobuf.Value(protobuf.Value.OneofValue.RecordValue(protobuf.Record(entries.mapValues(toProtoType[protobuf.Value]))))
        case types.ListValue(entries) => protobuf.Value(protobuf.Value.OneofValue.ListValue(protobuf.List(entries.map(toProtoType[protobuf.Value]))))
      }

      case o => throw new IllegalStateException(s"Cannot serialize object $o")
    }
  }

  def toDomainType[T](serializedMessage: GeneratedMessage): T = toDomain(serializedMessage).asInstanceOf[T]

  def toDomain(serializedMessage: GeneratedMessage): AnyRef = {
    serializedMessage match {

      case msg: SerializedData =>

        objectSerializer.deserializeObject(msg)

      case protobuf.RuntimeEvent(Some(name), ingredients) =>
        core.RuntimeEvent(name, readIngredients(ingredients))

      case protobuf.ProcessState(Some(id), ingredients, events) =>
        core.ProcessState(id, readIngredients(ingredients).toMap, events.toList)

      case protobuf.PetriNet(protoNodes, protoEdges) =>

        val nodes = protoNodes.map { n =>

          import protobuf.Node.OneofNode

          n.oneofNode match {

            case OneofNode.Place(protobuf.Place(Some(label), Some(placeType), limit)) =>
              val p = il.petrinet.Place(label, toDomainPlaceType(placeType, limit))
              Left(p)

            case OneofNode.EventTransition(protobuf.EventTransition(Some(eventDescriptor), Some(isSensoryEvent), maxFiringLimit)) =>
              Right(il.petrinet.EventTransition(toDomainType[il.EventDescriptor](eventDescriptor), isSensoryEvent, maxFiringLimit))

            case OneofNode.IntermediateTransition(protobuf.IntermediateTransition(Some(label))) =>
              Right(il.petrinet.IntermediateTransition(label))

            case OneofNode.MissingEventTransition(protobuf.MissingEventTransition(Some(label))) =>
              Right(il.petrinet.MissingEventTransition(label))

            case OneofNode.MultiFacilitatorTransition(protobuf.MultiFacilitatorTransition(Some(label))) =>
              Right(il.petrinet.MultiFacilitatorTransition(label))

            case OneofNode.InteractionTransition(t: protobuf.InteractionTransition) =>

              Right(il.petrinet.InteractionTransition(
                eventsToFire = t.eventsToFire.map(toDomainType[il.EventDescriptor]),
                originalEvents = t.originalEvents.map(toDomainType[il.EventDescriptor]),
                providedIngredientEvent = t.providedIngredientEvent.map(toDomainType[il.EventDescriptor]),
                requiredIngredients = t.requiredIngredients.map(toDomainType[il.IngredientDescriptor]),
                interactionName = t.interactionName.getOrMissing("interactionName"),
                originalInteractionName = t.originalInteractionName.getOrMissing("originalInteractionName"),
                actionType = if (t.isSieve.getOrElse(false)) ActionType.SieveAction else ActionType.InteractionAction,
                predefinedParameters = t.predefinedParameters.mapValues(toDomainType[Value]),
                maximumInteractionCount = t.maximumInteractionCount,
                failureStrategy = t.failureStrategy.map(toDomainType[il.failurestrategy.InteractionFailureStrategy]).getOrMissing("failureStrategy"),
                eventOutputTransformers = t.eventOutputTransformers.mapValues(toDomainType[il.EventOutputTransformer])
              ))

            case other => throw new IllegalStateException(s"Unknown node type: $other")
          }
        }

        val params = protoEdges.map {

          case protobuf.Edge(Some(from), Some(to), Some(weight), eventAllowed) =>
            val fromNode = nodes.apply(from.toInt)
            val toNode = nodes.apply(to.toInt)
            val edge = il.petrinet.Edge[Any](eventAllowed)

            WLDiEdge[Any, Any](fromNode, toNode)(weight, edge)
          case other =>
            throw new IllegalArgumentException(s"missing data in: $other")
        }

        scalax.collection.immutable.Graph(params: _*)

      case msg: protobuf.Type =>

        import Type.OneofType

        msg.`oneofType` match {
          case OneofType.Primitive(PrimitiveType.BOOLEAN) => types.PrimitiveType(classOf[Boolean])
          case OneofType.Primitive(PrimitiveType.BOOLEAN_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Boolean])
          case OneofType.Primitive(PrimitiveType.BYTE) => types.PrimitiveType(classOf[Byte])
          case OneofType.Primitive(PrimitiveType.BYTE_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Byte])
          case OneofType.Primitive(PrimitiveType.SHORT) => types.PrimitiveType(classOf[Short])
          case OneofType.Primitive(PrimitiveType.SHORT_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Short])
          case OneofType.Primitive(PrimitiveType.CHARACTER_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Character])
          case OneofType.Primitive(PrimitiveType.CHARACTER) => types.PrimitiveType(classOf[Char])
          case OneofType.Primitive(PrimitiveType.INTEGER) => types.PrimitiveType(classOf[Integer])
          case OneofType.Primitive(PrimitiveType.INT) => types.PrimitiveType(classOf[Int])
          case OneofType.Primitive(PrimitiveType.LONG) => types.PrimitiveType(classOf[Long])
          case OneofType.Primitive(PrimitiveType.LONG_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Long])
          case OneofType.Primitive(PrimitiveType.FLOAT) => types.PrimitiveType(classOf[Float])
          case OneofType.Primitive(PrimitiveType.FLOAT_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Float])
          case OneofType.Primitive(PrimitiveType.DOUBLE) => types.PrimitiveType(classOf[Double])
          case OneofType.Primitive(PrimitiveType.DOUBLE_PRIMITIVE) => types.PrimitiveType(classOf[java.lang.Double])
          case OneofType.Primitive(PrimitiveType.STRING) => types.PrimitiveType(classOf[String])
          case OneofType.Primitive(PrimitiveType.BIG_DECIMAL_SCALA) => types.PrimitiveType(classOf[BigDecimal])
          case OneofType.Primitive(PrimitiveType.BIG_DECIMAL_JAVA) => types.PrimitiveType(classOf[java.math.BigDecimal])
          case OneofType.Primitive(PrimitiveType.BIG_INT_SCALA) => types.PrimitiveType(classOf[BigInt])
          case OneofType.Primitive(PrimitiveType.BIG_INT_JAVA) => types.PrimitiveType(classOf[java.math.BigInteger])
          case OneofType.Primitive(PrimitiveType.BYTE_ARRAY) => types.PrimitiveType(classOf[Array[Byte]])
          case OneofType.Primitive(PrimitiveType.JODA_DATETIME) => types.PrimitiveType(classOf[time.DateTime])
          case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATE) => types.PrimitiveType(classOf[time.LocalDate])
          case OneofType.Primitive(PrimitiveType.JODA_LOCAL_DATETIME) => types.PrimitiveType(classOf[time.LocalDateTime])

          case OneofType.Optional(OptionalType(Some(value))) => types.OptionType(toDomainType[types.Type](value))

          case OneofType.List(ListType(Some(value))) => types.ListType(toDomainType[types.Type](value))

          case OneofType.Record(RecordType(fields)) =>
            val mapped = fields.map {
              case protobuf.RecordField(Some(name), Some(fieldType)) =>
                val `type` = toDomainType[types.Type](fieldType)
                types.RecordField(name, `type`)

              case _ => throw new IllegalStateException(s"Invalid value for record field (properties may not be None)")
            }

            types.RecordType(mapped)

          case OneofType.Map(MapType(Some(value))) => types.MapType(toDomainType[types.Type](value))

          case OneofType.Enum(EnumType(options)) => types.EnumType(options.toSet)

          case _ => throw new IllegalStateException(s"Proto message with missing fields: $msg")
        }

      case msg: protobuf.Value =>

        import protobuf.Value.OneofValue

        msg.oneofValue match {
          case OneofValue.NullValue(_) => types.NullValue
          case OneofValue.BooleanValue(bool) => types.PrimitiveValue(bool)
          case OneofValue.ByteValue(byte) => types.PrimitiveValue(byte.toByte)
          case OneofValue.ShortValue(short) => types.PrimitiveValue(short.toShort)
          case OneofValue.CharValue(char) => types.PrimitiveValue(char.toChar)
          case OneofValue.IntValue(int) => types.PrimitiveValue(int)
          case OneofValue.LongValue(long) => types.PrimitiveValue(long)
          case OneofValue.FloatValue(float) => types.PrimitiveValue(float)
          case OneofValue.DoubleValue(double) => types.PrimitiveValue(double)
          case OneofValue.StringValue(string) => types.PrimitiveValue(string)
          case OneofValue.BigDecimalScalaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal))
          case OneofValue.BigDecimalJavaValue(bigdecimal) => types.PrimitiveValue(BigDecimal(bigdecimal).bigDecimal)
          case OneofValue.BigIntScalaValue(bigint) => types.PrimitiveValue(BigInt(bigint))
          case OneofValue.BigIntJavaValue(bigint) => types.PrimitiveValue(BigInt(bigint).bigInteger)
          case OneofValue.ByteArrayValue(byteArray) => types.PrimitiveValue(byteArray.toByteArray)
          case OneofValue.JodaDatetimeValue(date) => types.PrimitiveValue(ISODateTimeFormat.dateTime().parseDateTime(date))
          case OneofValue.JodaLocaldateValue(date) => types.PrimitiveValue(LocalDate.parse(date))
          case OneofValue.JodaLocaldatetimeValue(date) => types.PrimitiveValue(LocalDateTime.parse(date))
          case OneofValue.RecordValue(Record(fields)) => types.RecordValue(fields.mapValues(toDomainType[types.Value]))
          case OneofValue.ListValue(List(entries)) => types.ListValue(entries.map(toDomainType[types.Value]).toList)
          case OneofValue.Empty => throw new IllegalStateException("Empty value cannot be deserializialized")
        }

      case fs: protobuf.InteractionFailureStrategy => fs.oneofType match {
        case protobuf.InteractionFailureStrategy.OneofType.BlockInteraction(_) =>
          il.failurestrategy.BlockInteraction
        case protobuf.InteractionFailureStrategy.OneofType.FireEventAfterFailure(protobuf.FireEventAfterFailure(Some(event))) =>
          il.failurestrategy.FireEventAfterFailure(toDomain(event).asInstanceOf[il.EventDescriptor])
        case protobuf.InteractionFailureStrategy.OneofType.RetryWithIncrementalBackoff(
            protobuf.RetryWithIncrementalBackoff(Some(initialTimeout), Some(backoff), Some(maximumRetries), maxBetween, exhaustedEvent)
          ) =>
          il.failurestrategy.RetryWithIncrementalBackoff(
            initialTimeout = Duration(initialTimeout, TimeUnit.MILLISECONDS),
            backoffFactor = backoff,
            maximumRetries = maximumRetries,
            maxTimeBetweenRetries = maxBetween.map(Duration(_, TimeUnit.MILLISECONDS)),
            retryExhaustedEvent = exhaustedEvent.map(toDomain(_).asInstanceOf[il.EventDescriptor]))
        case f => throw new IllegalStateException(s"Unknown failure strategy $f")
      }

      case protobuf.EventDescriptor(Some(name), protoIngredients) =>
        il.EventDescriptor(name, protoIngredients.map(e => toDomain(e).asInstanceOf[il.IngredientDescriptor]))

      case protobuf.IngredientDescriptor(Some(name), Some(ingredientType)) =>
        il.IngredientDescriptor(name, toDomain(ingredientType).asInstanceOf[types.Type])

      case protobuf.CompiledRecipe(Some(name), Some(graphMsg), producedTokens, validationErrors, eventReceiveMillis, retentionMillis) =>

        val eventReceivePeriod = eventReceiveMillis.map(Duration(_, TimeUnit.MILLISECONDS))
        val retentionPeriod = retentionMillis.map(Duration(_, TimeUnit.MILLISECONDS))

        val graph = toDomain(graphMsg).asInstanceOf[scalax.collection.immutable.Graph[Node, WLDiEdge]]
        val petriNet: RecipePetriNet = ScalaGraphPetriNet(graph)
        val initialMarking = producedTokens.foldLeft(Marking.empty[il.petrinet.Place]) {
          case (accumulated, protobuf.ProducedToken(Some(placeId), Some(_), Some(count), _)) ⇒ // Option[SerializedData] is always None, and we don't use it here.
            val place = petriNet.places.getById(placeId, "place in petrinet").asInstanceOf[il.petrinet.Place[Any]]
            val value = null // Values are not serialized (not interested in) in the serialized recipe
            accumulated.add(place, value, count)
          case _ ⇒ throw new IllegalStateException("Missing data in persisted ProducedToken")
        }

        CompiledRecipe(name, petriNet, initialMarking, validationErrors, eventReceivePeriod, retentionPeriod)

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

      case protobuf.EventOutputTransformer(newEventName, ingredientRenames) =>
        il.EventOutputTransformer(newEventName.getOrMissing("newEventName"), ingredientRenames)

      case _ => throw new IllegalStateException(s"Unknown protobuf message: $serializedMessage")

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

  private def toDomainPlaceType(protoPlaceType: protobuf.PlaceType, limit: Option[Int]) = protoPlaceType match {
    case protobuf.PlaceType.IngredientPlace => il.petrinet.Place.IngredientPlace
    case protobuf.PlaceType.InteractionEventOutputPlace => il.petrinet.Place.InteractionEventOutputPlace
    case protobuf.PlaceType.FiringLimiterPlace => il.petrinet.Place.FiringLimiterPlace(limit.getOrMissing("firing limit"))
    case protobuf.PlaceType.EventPreconditionPlace => il.petrinet.Place.EventPreconditionPlace
    case protobuf.PlaceType.EventOrPreconditionPlace => il.petrinet.Place.EventOrPreconditionPlace
    case protobuf.PlaceType.IntermediatePlace => il.petrinet.Place.IntermediatePlace
    case protobuf.PlaceType.EmptyEventIngredientPlace => il.petrinet.Place.EmptyEventIngredientPlace
    case protobuf.PlaceType.MultiTransitionPlace => il.petrinet.Place.MultiTransitionPlace
    case _ => throw new IllegalStateException(s"Unknown protobuf message: $protoPlaceType")
  }

}
