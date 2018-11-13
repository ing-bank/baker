package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.petrinet.api._
import com.ing.baker.runtime.actor.serialization.Encryption._
import com.ing.baker.runtime.actor.serialization.ProtoEventAdapterSpec._
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

    def mapOf[K, V](keyGen: Gen[K], valueGen: Gen[V]): Gen[Map[K, V]] = Gen.mapOf(GenUtil.tuple(keyGen, valueGen))
  }

  val recipeIdGen: Gen[String] = Gen.uuid.map(_.toString)
  val processIdGen: Gen[String] = Gen.uuid.map(_.toString)
  val timestampGen: Gen[Long] = Gen.chooseNum[Long](0, Long.MaxValue)

  object IntermediateLanguage {

    val eventNameGen: Gen[String] = Gen.alphaStr
    val finiteDurationGen: Gen[FiniteDuration] = Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))
    val allTypesRecipe = RecipeCompiler.compileRecipe(AllTypeRecipe.recipe)

    val recipeGen: Gen[CompiledRecipe] = Gen.const(allTypesRecipe)
  }

  object Runtime {

    import com.ing.baker.runtime.core._

    val eventNameGen: Gen[String] = Gen.alphaStr
    val ingredientNameGen: Gen[String] = Gen.alphaStr
    val ingredientsGen = GenUtil.tuple(ingredientNameGen, Types.anyValueGen)

    val runtimeEventGen = for {
      eventName <- eventNameGen
      ingredients <- Gen.listOf(ingredientsGen)
    } yield RuntimeEvent(eventName, ingredients)

    val processStateGen = for {
      processId <- processIdGen
      ingredients <- Gen.mapOf(ingredientsGen)
      eventNames <- Gen.listOf(eventNameGen)
    } yield ProcessState(processId, ingredients, eventNames)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(runtimeEventGen, processStateGen)
  }

  object RecipeManager {

    import IntermediateLanguage._
    import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._

    val addRecipeGen: Gen[AddRecipe] = recipeGen.map(AddRecipe(_))
    val getRecipeGen: Gen[GetRecipe] = recipeIdGen.map(GetRecipe(_))
    val recipeFoundGen: Gen[RecipeFound] = for {
      compiledRecipe <- IntermediateLanguage.recipeGen
      timestamp <- timestampGen
    } yield RecipeFound(compiledRecipe, timestamp)


    val noRecipeFoundGen: Gen[NoRecipeFound] = recipeIdGen.map(NoRecipeFound(_))
    val addRecipeResponseGen: Gen[AddRecipeResponse] = recipeIdGen.map(AddRecipeResponse(_))
    val getAllRecipesGen: Gen[GetAllRecipes.type] = Gen.const(GetAllRecipes)

    val recipeEntriesGen = GenUtil.tuple(recipeIdGen, recipeGen)

    val recipeInformationGen: Gen[RecipeInformation] = for {
      compiledRecipe <- recipeGen
      timestamp <- timestampGen
    } yield RecipeInformation(compiledRecipe, timestamp)

    val allRecipesGen: Gen[AllRecipes] = Gen.listOf(recipeInformationGen).map(AllRecipes(_))


    val messagesGen: Gen[AnyRef] = Gen.oneOf(
      addRecipeGen, getRecipeGen, recipeFoundGen, noRecipeFoundGen, addRecipeResponseGen, getAllRecipesGen, allRecipesGen
    )
  }

  object ProcessIndex {

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
      event <- Runtime.runtimeEventGen
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

    val transitionIdGen = Gen.posNum[Long]
    val placeIdGen = Gen.posNum[Long]
    val jobIdGen = Gen.posNum[Long]
    val processStateGen = Runtime.processStateGen
    val tokenDataGen = Gen.alphaStr
    val transitionInputGen = Runtime.runtimeEventGen
    val correlationIdGen = Gen.uuid.map(_.toString)

    val multiSetGen: Gen[MultiSet[Any]] = Gen.nonEmptyMap[Any, Int](GenUtil.tuple(tokenDataGen, Gen.posNum[Int]))
    val markingDataGen: Gen[Marking[Id]] = Gen.mapOf(GenUtil.tuple(placeIdGen, multiSetGen))

    val getStateGen = Gen.const(GetState)
    val stopGen = Gen.oneOf(true, false).map(Stop(_))
    val initializeGen = for {
      marking <- markingDataGen
      state <- processStateGen
    } yield Initialize(marking, state)

    val uninitializedGen = processIdGen.map(Uninitialized(_))
    val alreadyInitializedGen = processIdGen.map(AlreadyInitialized(_))

    val initializedGen = for {
      marking <- markingDataGen
      state <- processStateGen
    } yield Initialized(marking, state)

    val fireTransitionGen = for {
      transitionId <- transitionIdGen
      input <- transitionInputGen
      correlationId <- Gen.option(correlationIdGen)
    } yield FireTransition(transitionId, input, correlationId)

    val alreadyReceived = correlationIdGen.map(AlreadyReceived(_))

    val failureStrategyGen: Gen[ExceptionStrategy] = Gen.oneOf(
      Gen.const(ExceptionStrategy.BlockTransition),
      Gen.const(ExceptionStrategy.Fatal),
      Gen.posNum[Long].map(delay => ExceptionStrategy.RetryWithDelay(delay)),
      for {
        marking <- markingDataGen
        output <- Runtime.runtimeEventGen
      } yield ExceptionStrategy.Continue(marking, output)
    )

    val exceptionStateGen: Gen[ExceptionState] = for {
      failureCount <- Gen.posNum[Int]
      failureReason <- Gen.alphaStr
      failureStrategy <- failureStrategyGen
    } yield ExceptionState(failureCount, failureReason, failureStrategy)

    val jobStateGen: Gen[JobState] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      consumed <- markingDataGen
      input <- Runtime.runtimeEventGen
      exceptionState <- Gen.option(exceptionStateGen)
    } yield JobState(jobId, transitionId, consumed, input, exceptionState)

    val instanceStateGen = for {
      sequenceNr <- Gen.posNum[Int]
      marking <- markingDataGen
      state <- processStateGen
      jobs <- Gen.mapOf(jobStateGen.map(job => job.id -> job))
    } yield InstanceState(sequenceNr, marking, state, jobs)

    val transitionFiredGen = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consumed <- markingDataGen
      produced <- markingDataGen
      state <- instanceStateGen
      newJobs <- Gen.listOf(jobIdGen).map(_.toSet)
      output <- Runtime.runtimeEventGen
    } yield TransitionFired(jobId, transitionId, correlationId, consumed, produced, state, newJobs, output)

    val transitionFailedGen = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consume <- markingDataGen
      input <- Runtime.runtimeEventGen
      reason <- Gen.alphaStr
      strategy <- failureStrategyGen
    } yield TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy)

    val transitionNotEnabledGen = for {
      transitionId <- transitionIdGen
      reason <- Gen.alphaStr
    } yield TransitionNotEnabled(transitionId, reason)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(getStateGen, stopGen, initializeGen, initializedGen, uninitializedGen,
      alreadyInitializedGen, fireTransitionGen, transitionFiredGen, transitionFailedGen, transitionNotEnabledGen)
  }

  object Types {

    import com.ing.baker.types._
    import com.ing.baker.types.modules.PrimitiveModuleSpec._

    val fieldNameGen = Gen.alphaStr

    val primitiveTypeGen: Gen[Type] = Gen.oneOf(types.primitiveTypes.toSeq)

    val fieldTypeGen = primitiveTypeGen

    val recordTypeEntries = for {
      fieldName <- fieldNameGen
      fieldType <- fieldTypeGen
    } yield RecordField(fieldName, fieldType)

    val recordTypeGen = Gen.listOf(recordTypeEntries).map(RecordType(_))
    val listTypeGen = primitiveTypeGen.map(ListType(_))
    val mapTypeGen = primitiveTypeGen.map(MapType(_))
    val optionTypeGen = primitiveTypeGen.map(OptionType(_))

    val anyTypeGen = Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

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

    val anyValueGen: Gen[Value] = Gen.oneOf(primitiveValuesGen, listValueGen, recordValueGen, nullValueGen)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(anyValueGen, anyTypeGen)
  }
}

class ProtoEventAdapterSpec extends WordSpecLike with Checkers with Matchers with BeforeAndAfterAll {

  val actorSystem = ActorSystem()

  val testAdapter = new ProtoEventAdapterImpl(actorSystem, NoEncryption)

  val minSuccessfulTests = 100

  "The Types protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(Types.messagesGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The Runtime protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(Runtime.messagesGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

  "The IntermediateLanguage protobuf serialization module" should {

    "be able to translate all messages to/from protobuf" in {

      val property = transitivityProperty(IntermediateLanguage.recipeGen, testAdapter)

      check(property, defaultVerbose.withMinSuccessfulTests(minSuccessfulTests))
    }
  }

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

      val property = transitivityProperty(ProcessInstance.messagesGen, testAdapter)

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
