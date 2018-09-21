package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.petrinet.api.MultiSet
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol.{Initialize, MarkingData}
import com.ing.baker.runtime.actor.serialization.Encryption._
import com.ing.baker.runtime.actor.serialization.ProtoEventAdapterSpec._
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.types.PrimitiveValue
import com.ing.baker.{AllTypeRecipe, types}
import javax.crypto.BadPaddingException
import org.scalacheck.Gen
import org.scalacheck.Prop.{BooleanOperators, forAll}
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalatest.prop.Checkers
import org.scalatest.{BeforeAndAfterAll, Matchers, WordSpecLike}

import scala.concurrent.duration._

object ProtoEventAdapterSpec {

  def transitivityProperty[T <: AnyRef](gen: Gen[T], adapter: ProtoEventAdapterImpl) = forAll(gen) { originalObject =>

    val serialized = adapter.toProtoMessage(originalObject)
    val deserializedObject = adapter.toDomainObject(serialized)

    (originalObject == deserializedObject) :| s"$originalObject != $deserializedObject"
  }

  object GenUtil {

    def tuple[K, V](keyGen: Gen[K], valueGen: Gen[V]): Gen[(K, V)] = for {
      key <- keyGen
      value <- valueGen
    } yield key -> value
  }

  object IntermediateLanguage {

    import Types._

    val recipeIdGen: Gen[String] = Gen.uuid.map(_.toString)
    val processIdGen: Gen[String] = Gen.uuid.map(_.toString)
    val ingredientNameGen: Gen[String] = Gen.alphaStr
    val eventNameGen: Gen[String] = Gen.alphaStr
    val finiteDurationGen: Gen[FiniteDuration] = Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))

    val ingredientsGen = GenUtil.tuple(ingredientNameGen, valuesGen)

    val runtimeEventGen = for {
      eventName <- eventNameGen
      ingredients <- Gen.listOf(ingredientsGen)
    } yield RuntimeEvent(eventName, ingredients)

    val allTypesRecipe = RecipeCompiler.compileRecipe(AllTypeRecipe.recipe)
    val recipeGen: Gen[CompiledRecipe] = Gen.const(allTypesRecipe)
  }

  object RecipeManager {

    import IntermediateLanguage._
    import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._

    val addRecipeGen: Gen[AddRecipe] = recipeGen.map(AddRecipe(_))
    val getRecipeGen: Gen[GetRecipe] = recipeIdGen.map(GetRecipe(_))
    val recipeFoundGen: Gen[RecipeFound] = recipeGen.map(RecipeFound(_))
    val noRecipeFoundGen: Gen[NoRecipeFound] = recipeIdGen.map(NoRecipeFound(_))
    val addRecipeResponseGen: Gen[AddRecipeResponse] = recipeIdGen.map(AddRecipeResponse(_))
    val getAllRecipesGen: Gen[GetAllRecipes.type] = Gen.const(GetAllRecipes)

    val recipeEntriesGen = GenUtil.tuple(recipeIdGen, recipeGen)

    val allRecipesGen: Gen[AllRecipes] = Gen.mapOfN(2, recipeEntriesGen).map(AllRecipes(_))

    val messagesGen: Gen[AnyRef] = Gen.oneOf(
      addRecipeGen, getRecipeGen, recipeFoundGen, noRecipeFoundGen, addRecipeResponseGen, getAllRecipesGen, allRecipesGen
    )
  }

  object ProcessIndex {

    import IntermediateLanguage._
    import com.ing.baker.runtime.actor.process_index.ProcessIndex._
    import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol._

    val processStatusGen: Gen[ProcessStatus] = Gen.oneOf(Active, Deleted)
    val createdTimeGen: Gen[Long] = Gen.chooseNum[Long](0, Long.MaxValue)

    val actorMetadataGen: Gen[ActorMetadata] = for {
      recipeId <- recipeIdGen
      processId <- processIdGen
      createdTime <- createdTimeGen
      status <- processStatusGen
    } yield ActorMetadata(recipeId, processId, createdTime, status)

    val getIndexGen = Gen.const(GetIndex)
    val indexGen: Gen[Index] = Gen.listOf(actorMetadataGen).map(Index(_))

    val createProcessGen = for {
      recipeId <- recipeIdGen
      processId <- processIdGen
    } yield CreateProcess(recipeId, processId)

    val processEventGen = for {
      processId <- processIdGen
      event <- runtimeEventGen
      correlationId <- Gen.option(processIdGen)
      waitForRetries <- Gen.oneOf(true, false)
      timeout <- Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))
    } yield ProcessEvent(processId, event, correlationId, waitForRetries, timeout)

//    val dummySourceRef: SourceRef[Any] = Await.result(Source.single("").runWith(StreamRefs.sourceRef()), 2 seconds)
//
//    val processEventResponseGen = for {
//      processId <- processIdGen
//      sourceRef <- Gen.const(dummySourceRef)
//    } yield ProcessEventResponse(processId, sourceRef)

    val getProcessStateGen = processIdGen.map(GetProcessState(_))
    val getCompiledRecipeGen = processIdGen.map(GetCompiledRecipe(_))
    val receivePeriodExpiredGen = processIdGen.map(ReceivePeriodExpired(_))
    val invalidEventGen = for {
      processId <- processIdGen
      msg <- Gen.alphaStr
    } yield InvalidEvent(processId, msg)

    val processDeletedGen = processIdGen.map(ProcessDeleted(_))
    val noSuchProcessGen = processIdGen.map(NoSuchProcess(_))
    val processAlreadyExistsGen = processIdGen.map(ProcessAlreadyExists(_))

    val messagesGen: Gen[AnyRef] = Gen.oneOf(getIndexGen, indexGen, createProcessGen, processEventGen,
      getProcessStateGen, getCompiledRecipeGen, receivePeriodExpiredGen, invalidEventGen, processDeletedGen,
      noSuchProcessGen, processAlreadyExistsGen)
  }

  object ProcessInstance {

    import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._
    import Types._

    val transitionIdGen = Gen.posNum[Long]
    val placeIdGen = Gen.posNum[Long]
    val processStateGen = primitiveValuesGen
    val transitionInputGen = IntermediateLanguage.runtimeEventGen
    val correlationIdGen = Gen.uuid.map(_.toString)

    val multiSetGen: Gen[MultiSet[_]] = Gen.mapOfN[Any, Int](5, GenUtil.tuple(processStateGen, Gen.posNum[Int]))
    val markingDataGen: Gen[MarkingData] = Gen.mapOfN(1, GenUtil.tuple(placeIdGen, multiSetGen))

    val getStateGen = Gen.const(GetState)
    val stopGen = Gen.oneOf(true, false).map(Stop(_))
    val initializeGen = for {
      marking <- markingDataGen
      state <- processStateGen
    } yield Initialize(marking, state)

    val fireTransitionGen = for {
      transitionId <- transitionIdGen
      input <- transitionInputGen
      correlationId <- Gen.option(correlationIdGen)
    } yield FireTransition(transitionId, input, correlationId)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(getStateGen, stopGen, initializeGen, fireTransitionGen)
  }

  object Types {

    import com.ing.baker.types._

    val fieldNameGen = Gen.alphaStr

    val primitiveTypeGen: Gen[Type] = Gen.oneOf(
      types.supportedPrimitiveClasses.toSeq.map(clazz => PrimitiveType(clazz))
    )

    val fieldTypeGen = primitiveTypeGen

    val recordTypeEntries = for {
      fieldName <- fieldNameGen
      fieldType <- fieldTypeGen
    } yield RecordField(fieldName, fieldType)

    val recordTypeGen = Gen.listOf(recordTypeEntries).map(RecordType(_))
    val listTypeGen = primitiveTypeGen.map(ListType(_))
    val mapTypeGen = primitiveTypeGen.map(MapType(_))
    val optionTypeGen = primitiveTypeGen.map(OptionType(_))

    val typesGen = Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

    val intGen: Gen[Int] = Gen.chooseNum[Int](Integer.MIN_VALUE, Integer.MAX_VALUE)
    val langIntegerGen: Gen[java.lang.Integer] = intGen.map(Int.box(_))
    val longGen: Gen[Long] = Gen.chooseNum[Long](Long.MinValue, Long.MaxValue)
    val langLongGen: Gen[java.lang.Long] = Gen.chooseNum[Long](Long.MinValue, Long.MaxValue).map(Long.box(_))
    val shortGen: Gen[Short] = Gen.chooseNum[Short](Short.MinValue, Short.MaxValue)
    val langShortGen: Gen[java.lang.Short] = shortGen.map(Short.box(_))
    val floatGen: Gen[Float] = Gen.chooseNum(Float.MinValue, Float.MaxValue)
    val langFloatGen: Gen[java.lang.Float] = floatGen.map(Float.box(_))
    val doubleGen: Gen[Double] = Gen.chooseNum[Double](Double.MinValue, Double.MaxValue)
    val langDoubleGen: Gen[java.lang.Double] = doubleGen.map(Double.box(_))
    val stringGen: Gen[String] = Gen.alphaStr
    val bigIntGen: Gen[BigInt] = longGen.map(BigInt(_))
    val javaBigIntGen: Gen[java.math.BigInteger] = bigIntGen.map(_.bigInteger)
    val bigDecimalGen: Gen[BigDecimal] = doubleGen.map(BigDecimal(_))
    val javaBigDecimalGen: Gen[java.math.BigDecimal] = bigDecimalGen.map(_.bigDecimal)
    val byteArrayGen: Gen[Array[Byte]] = Gen.listOf(intGen.map(_.toByte)).map(_.toArray)

    val primitiveJavaObjGen: Gen[Any] = Gen.oneOf(
      intGen, langIntegerGen, longGen, langLongGen, shortGen, langShortGen, floatGen, langFloatGen,
      doubleGen, langDoubleGen, stringGen, bigIntGen, javaBigIntGen, bigDecimalGen, javaBigDecimalGen, byteArrayGen
    )

    val primitiveValuesGen: Gen[Value] = primitiveJavaObjGen.map(PrimitiveValue(_))
    val listValueGen: Gen[Value] = Gen.listOf(primitiveValuesGen).map(ListValue(_))
    val nullValueGen: Gen[Value] = Gen.const(NullValue)

    val recordValueEntries = for {
      fieldName <- fieldNameGen
      fieldValue <- primitiveValuesGen
    } yield fieldName -> fieldValue

    val recordValueGen: Gen[Value] = Gen.mapOf(recordValueEntries).map(RecordValue(_))

    val valuesGen: Gen[Value] = Gen.oneOf(primitiveValuesGen, listValueGen, recordValueGen, nullValueGen)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(valuesGen, typesGen)
  }
}

@deprecated("marked deprecated because of -XFatal-Warnings and deprecated sieves", "1.4.0")
class ProtoEventAdapterSpec extends WordSpecLike with Checkers with Matchers with BeforeAndAfterAll {

  val actorSystem = ActorSystem()

  val testAdapter = new ProtoEventAdapterImpl(actorSystem, NoEncryption)

  val minSuccessfulTests = 100

  "The RecipeManager protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(RecipeManager.messagesGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The ProcessIndex protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(ProcessIndex.messagesGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The ProcessInstance protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      def initTransitivityProperty(gen: Gen[Initialize], adapter: ProtoEventAdapterImpl) = forAll(gen) { originalObject =>

        val serialized = adapter.toProtoMessage(originalObject)
        val deserializedObject = adapter.toDomainObject(serialized)

        if (originalObject != deserializedObject) {

          val initA = originalObject
          val initB = deserializedObject.asInstanceOf[Initialize]

          println("marking equal: " + (initA.marking == initB.marking))
          println("state equal: " + (initA.state == initB.state))

          initA.marking.foreach {
            case (placeId, multiSet) =>
              val multiSetB = initB.marking(placeId).asInstanceOf[MultiSet[Any]]
              val multiSetA = multiSet.asInstanceOf[MultiSet[Any]]

              if (multiSetA != multiSetB) {
                println("not equal for " + placeId)
                println(s"${multiSetA.getClass}")
                println(s"${multiSetB.getClass}")
                multiSetA.foreach { case (obj, count) =>
                  if (!multiSetB.contains(obj)) println(s"$obj (class ${obj.asInstanceOf[PrimitiveValue].value.getClass}) is not found")
                  else if (multiSetB(obj) != count) println(s"$obj (class ${obj.asInstanceOf[PrimitiveValue].value.getClass}) has different count (${multiSetB(obj)} != $count")
                }
                multiSetB.foreach { case (obj, count) =>
                  if (!multiSetA.contains(obj)) println(s"$obj (class ${obj.asInstanceOf[PrimitiveValue].value.getClass}) is not found")
                  else if (multiSetA(obj) != count) println(s"$obj (class ${obj.asInstanceOf[PrimitiveValue].value.getClass}) has different count (${multiSetA(obj)} != $count")
                }
              }
          }
        }

        (originalObject == deserializedObject) :| s"$originalObject != $deserializedObject"
      }

//      val property = transitivityProperty(ProcessInstance.messagesGen, testAdapter)
      val property = initTransitivityProperty(ProcessInstance.initializeGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The Types protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(Types.messagesGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The ProtoEventAdapter" should {
    "serialize/deserialize data with encryption" in {
      val someEvent = "some event"
      val serializer1 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))
      val serializer2 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))

      val serializedData = serializer1.toProtoAny(someEvent)

      serializer2.toDomain[AnyRef](serializedData) shouldBe someEvent
    }

    "cannot deserialize data back if another encryption secret is used" in {
      val someEvent = "some event"
      val serializer1 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123456"))
      val serializer2 = new ProtoEventAdapterImpl(actorSystem, new AESEncryption("0123456789123459"))

      val serializedData = serializer1.toProtoAny(someEvent)

      // fails during decryption and throws this exception
      intercept[BadPaddingException] {
        serializer2.toDomain[AnyRef](serializedData)
      }
    }

    "serialize/deserialize data without encryption" in {
      val someEvent = "some event"
      val serializer1 = new ProtoEventAdapterImpl(actorSystem, NoEncryption)
      val serializer2 = new ProtoEventAdapterImpl(actorSystem, NoEncryption)

      val serializedData = serializer1.toProtoAny(someEvent)

      serializer2.toDomain[AnyRef](serializedData) shouldBe someEvent
    }
  }

  override def afterAll() = {
    super.afterAll()
    actorSystem.terminate()
  }
}
