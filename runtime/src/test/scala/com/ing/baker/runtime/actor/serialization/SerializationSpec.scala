package com.ing.baker.runtime.actor.serialization

import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.petrinet.api.{Id, Marking, MultiSet}
import com.ing.baker.runtime.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.actor.process_index.ProcessIndexProtocol
import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.actor.recipe_manager.RecipeManager.RecipeAdded
import org.scalacheck.Prop.forAll
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalacheck._
import org.scalatest.FunSuiteLike
import org.scalatest.prop.Checkers
import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol
import com.ing.baker.runtime.core.BakerResponseEventProtocol.{IndexInvalidEvent, IndexNoSuchProcess, IndexProcessDeleted, IndexReceivePeriodExpired, InstanceAlreadyReceived, InstanceTransitionFailed, InstanceTransitionFired, InstanceTransitionNotEnabled}
import com.ing.baker.runtime.core.{BakerResponseEventProtocol, ProcessState, RuntimeEvent}
import com.ing.baker.types.Value
import com.ing.baker.{AllTypeRecipe, types}

import scala.concurrent.duration._

class SerializationSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Checkers {

  val serializer: BakerTypedProtobufSerializer =
    SerializationExtension
      .get(system)
      .serializerByIdentity(101)
      .asInstanceOf[BakerTypedProtobufSerializer]

  def checkFor[A <: AnyRef](name: String, gen: Gen[A]): Unit = {
    test(s"$name typed serialization") {
      check(forAll(gen)(m =>
        m == serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))),
        defaultVerbose.withMinSuccessfulTests(10)
      )
    }
  }

  checkFor("core.RuntimeEvent", SerializationSpec.Runtime.runtimeEventGen)

  checkFor("core.ProcessState", SerializationSpec.Runtime.processStateGen)

  checkFor("ProcessIndex.GetShardIndex", SerializationSpec.ProcessIndex.getShardIndexGen)

  checkFor("ProcessIndex.ActorCreated", SerializationSpec.ProcessIndex.actorCreatedGen)

  checkFor("ProcessIndex.ActorDeleted", SerializationSpec.ProcessIndex.actorDeletedGen)

  checkFor("ProcessIndex.ActorPassivated", SerializationSpec.ProcessIndex.actorPassivatedGen)

  checkFor("ProcessIndex.ActorActivated", SerializationSpec.ProcessIndex.actorActivatedGen)

  checkFor("ProcessIndex.ActorMetadata", SerializationSpec.ProcessIndex.actorMetadataGen)

  test("ProcessIndexProtocol.GetIndex typed serialization") {
    val serialized = serializer.toBinary(ProcessIndexProtocol.GetIndex)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(ProcessIndexProtocol.GetIndex))
    ProcessIndexProtocol.GetIndex == deserialized
  }

  checkFor("ProcessIndexProtocol.Index", SerializationSpec.ProcessIndex.indexGen)

  checkFor("ProcessIndexProtocol.CreateProcess", SerializationSpec.ProcessIndex.createProcessGen)

  checkFor("ProcessIndexProtocol.ProcessEvent", SerializationSpec.ProcessIndex.processEventGen)

  checkFor("ProcessIndexProtocol.RetryBlockedInteraction", SerializationSpec.ProcessIndex.retryBlockedInteractionGen)

  checkFor("ProcessIndexProtocol.ResolveBlockedInteraction", SerializationSpec.ProcessIndex.resolveBlockedInteraction)

  checkFor("ProcessIndexProtocol.StopRetryingInteraction", SerializationSpec.ProcessIndex.stopRetryingInteractionGen)

  checkFor("ProcessInstance.TransitionFailed", SerializationSpec.ProcessInstance.transitionFailedGen)

  checkFor("RecipeManagerProtocol.AddRecipe", SerializationSpec.RecipeManager.addRecipeGen)

  checkFor("RecipeManagerProtocol.AddRecipeResponse", SerializationSpec.RecipeManager.addRecipeResponseGen)

  checkFor("RecipeManagerProtocol.GetRecipe", SerializationSpec.RecipeManager.getRecipeGen)

  checkFor("RecipeManagerProtocol.RecipeFound", SerializationSpec.RecipeManager.recipeFoundGen)

  checkFor("RecipeManagerProtocol.NoRecipeFound", SerializationSpec.RecipeManager.noRecipeFoundGen)

  checkFor("RecipeManagerProtocol.AllRecipes", SerializationSpec.RecipeManager.allRecipesGen)

  test("RecipeManagerProtocol.GetAllRecipes typed serialization") {
    val serialized = serializer.toBinary(RecipeManagerProtocol.GetAllRecipes)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(RecipeManagerProtocol.GetAllRecipes))
    RecipeManagerProtocol.GetAllRecipes == deserialized
  }

  checkFor("RecipeManager.RecipeAdded", SerializationSpec.RecipeManager.recipeAddedGen)

  checkFor("BakerResponseEventProtocol", SerializationSpec.BakerResponseStream.eventProtocolGen)

  checkFor("ProcessInstanceProtocol.Stop", SerializationSpec.ProcessInstance.stopGen)

  test("ProcessInstanceProtocol.GetState typed serialization") {
    val serialized = serializer.toBinary(ProcessInstanceProtocol.GetState)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(RecipeManagerProtocol.GetAllRecipes))
    ProcessInstanceProtocol.GetState == deserialized
  }

  checkFor("ProcessInstanceProtocol.InstanceState", SerializationSpec.ProcessInstance.instanceStateGen)

  checkFor("ProcessInstanceProtocol.Initialize", SerializationSpec.ProcessInstance.initializeGen)

  checkFor("ProcessInstanceProtocol.Initialized", SerializationSpec.ProcessInstance.initializedGen)

  checkFor("ProcessInstanceProtocol.Uninitialized", SerializationSpec.ProcessInstance.uninitializedGen)

  checkFor("ProcessInstanceProtocol.AlreadyInitialized", SerializationSpec.ProcessInstance.alreadyInitializedGen)

  checkFor("ProcessInstanceProtocol.FireTransition", SerializationSpec.ProcessInstance.fireTransitionGen)

  checkFor("ProcessInstanceProtocol.OverrideExceptionStrategy", SerializationSpec.ProcessInstance.overrideFailureGen)

  checkFor("ProcessInstanceProtocol.InvalidCommand", SerializationSpec.ProcessInstance.invalidCommandGen)

  checkFor("ProcessInstanceProtocol.AlreadyReceived", SerializationSpec.ProcessInstance.alreadyReceived)

  checkFor("ProcessInstanceProtocol.TransitionNotEnabled", SerializationSpec.ProcessInstance.transitionNotEnabledGen)

  checkFor("ProcessInstanceProtocol.TransitionFailed", SerializationSpec.ProcessInstance.transitionFailedGen)

  checkFor("ProcessInstanceProtocol.TransitionFired", SerializationSpec.ProcessInstance.transitionFiredGen)
  
}

object SerializationSpec {

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
    val allTypesRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(AllTypeRecipe.recipe)

    val recipeGen: Gen[CompiledRecipe] = Gen.const(allTypesRecipe)
  }

  object Runtime {

    import com.ing.baker.runtime.core._

    val eventNameGen: Gen[String] = Gen.alphaStr
    val ingredientNameGen: Gen[String] = Gen.alphaStr
    val ingredientsGen: Gen[(String, Value)] = GenUtil.tuple(ingredientNameGen, Types.anyValueGen)

    val runtimeEventGen: Gen[RuntimeEvent] = for {
      eventName <- eventNameGen
      ingredients <- Gen.listOf(ingredientsGen)
    } yield RuntimeEvent(eventName, ingredients)

    val processStateGen: Gen[ProcessState] = for {
      processId <- processIdGen
      ingredients <- Gen.mapOf(ingredientsGen)
      eventNames <- Gen.listOf(eventNameGen)
    } yield ProcessState(processId, ingredients, eventNames)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(runtimeEventGen, processStateGen)
  }

  object RecipeManager {

    import IntermediateLanguage._
    import com.ing.baker.runtime.actor.recipe_manager.RecipeManagerProtocol._

    val addRecipeGen: Gen[AddRecipe] = recipeGen.map(AddRecipe)
    val getRecipeGen: Gen[GetRecipe] = recipeIdGen.map(GetRecipe)
    val recipeFoundGen: Gen[RecipeFound] = for {
      compiledRecipe <- IntermediateLanguage.recipeGen
      timestamp <- timestampGen
    } yield RecipeFound(compiledRecipe, timestamp)


    val noRecipeFoundGen: Gen[NoRecipeFound] = recipeIdGen.map(NoRecipeFound)
    val addRecipeResponseGen: Gen[AddRecipeResponse] = recipeIdGen.map(AddRecipeResponse)
    val getAllRecipesGen: Gen[GetAllRecipes.type] = Gen.const(GetAllRecipes)

    val recipeEntriesGen: Gen[(String, CompiledRecipe)] = GenUtil.tuple(recipeIdGen, recipeGen)

    val recipeInformationGen: Gen[RecipeInformation] = for {
      compiledRecipe <- recipeGen
      timestamp <- timestampGen
    } yield RecipeInformation(compiledRecipe, timestamp)

    val allRecipesGen: Gen[AllRecipes] = Gen.listOf(recipeInformationGen).map(AllRecipes(_))

    val messagesGen: Gen[AnyRef] = Gen.oneOf(
      addRecipeGen, getRecipeGen, recipeFoundGen, noRecipeFoundGen, addRecipeResponseGen, getAllRecipesGen, allRecipesGen
    )

    val recipeAddedGen: Gen[RecipeAdded] =
      for {
        timestamp <- Gen.chooseNum(0l, 20000l)
        recipe <- recipeGen
      } yield RecipeAdded(recipe, timestamp)
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

    val getIndexGen: Gen[ProcessIndexProtocol.GetIndex.type] = Gen.const(GetIndex)
    val indexGen: Gen[Index] = Gen.listOf(actorMetadataGen).map(Index(_))

    val createProcessGen: Gen[CreateProcess] = for {
      recipeId <- recipeIdGen
      processId <- processIdGen
    } yield CreateProcess(recipeId, processId)

    val processEventGen: Gen[ProcessEvent] = for {
      processId <- processIdGen
      event <- Runtime.runtimeEventGen
      correlationId <- Gen.option(processIdGen)
      waitForRetries <- Gen.oneOf(true, false)
      timeout <- Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))
    } yield ProcessEvent(processId, event, correlationId, waitForRetries, timeout)

    val getProcessStateGen: Gen[GetProcessState] = processIdGen.map(GetProcessState)
    val getCompiledRecipeGen: Gen[GetCompiledRecipe] = processIdGen.map(GetCompiledRecipe)
    val receivePeriodExpiredGen: Gen[ReceivePeriodExpired] = processIdGen.map(ReceivePeriodExpired)
    val invalidEventGen: Gen[InvalidEvent] = for {
      processId <- processIdGen
      msg <- Gen.alphaStr
    } yield InvalidEvent(processId, msg)

    val processDeletedGen: Gen[ProcessDeleted] = processIdGen.map(ProcessDeleted)
    val noSuchProcessGen: Gen[NoSuchProcess] = processIdGen.map(NoSuchProcess)
    val processAlreadyExistsGen: Gen[ProcessAlreadyExists] = processIdGen.map(ProcessAlreadyExists)

    val retryBlockedInteractionGen: Gen[RetryBlockedInteraction] = for {
      processId <- processIdGen
      interactionName <- Gen.alphaStr
    } yield RetryBlockedInteraction(processId, interactionName)

    val resolveBlockedInteraction: Gen[ResolveBlockedInteraction] = for {
      processId <- processIdGen
      interactionName <- Gen.alphaStr
      event <- Runtime.runtimeEventGen
    } yield ResolveBlockedInteraction(processId, interactionName, event)

    val stopRetryingInteractionGen: Gen[StopRetryingInteraction] = for {
      processId <- processIdGen
      interactionName <- Gen.alphaStr
    } yield StopRetryingInteraction(processId, interactionName)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(getIndexGen, indexGen, createProcessGen, processEventGen,
      getProcessStateGen, getCompiledRecipeGen, receivePeriodExpiredGen, invalidEventGen, processDeletedGen,
      noSuchProcessGen, processAlreadyExistsGen, retryBlockedInteractionGen, resolveBlockedInteraction, stopRetryingInteractionGen)


    val identifierGen: Gen[String] = Gen.alphaNumStr

    val timestampGen: Gen[Long] = Gen.chooseNum(100000l, 1000000l)

    val getShardIndexGen: Gen[GetShardIndex] =
      identifierGen.map(GetShardIndex)

    val actorCreatedGen: Gen[ActorCreated] =
      for {
        recipeId <- identifierGen
        processId <- identifierGen
        timestamp <- timestampGen
      } yield ActorCreated(recipeId, processId, timestamp)

    val actorActivatedGen: Gen[ActorActivated] =
      identifierGen.map(ActorActivated)

    val actorPassivatedGen: Gen[ActorPassivated] =
      identifierGen.map(ActorPassivated)

    val actorDeletedGen: Gen[ActorDeleted] =
      identifierGen.map(ActorDeleted)

    val resolveBlockedInteractionGen: Gen[ResolveBlockedInteraction] =
      for {
        recipeId <- identifierGen
        processId <- identifierGen
        event <- Runtime.runtimeEventGen
      } yield ResolveBlockedInteraction(recipeId, processId, event)
  }

  object ProcessInstance {

    import com.ing.baker.runtime.actor.process_instance.ProcessInstanceProtocol._

    val transitionIdGen: Gen[Id] = Gen.posNum[Long]
    val placeIdGen: Gen[Id] = Gen.posNum[Long]
    val jobIdGen: Gen[Id] = Gen.posNum[Long]
    val processStateGen: Gen[ProcessState] = Runtime.processStateGen
    val tokenDataGen: Gen[String] = Gen.alphaStr
    val transitionInputGen: Gen[RuntimeEvent] = Runtime.runtimeEventGen
    val correlationIdGen: Gen[String] = Gen.uuid.map(_.toString)

    val multiSetGen: Gen[MultiSet[Any]] = Gen.nonEmptyMap[Any, Int](GenUtil.tuple(tokenDataGen, Gen.posNum[Int]))
    val markingDataGen: Gen[Marking[Id]] = Gen.mapOf(GenUtil.tuple(placeIdGen, multiSetGen))

    val getStateGen: Gen[ProcessInstanceProtocol.GetState.type] = Gen.const(GetState)
    val stopGen: Gen[Stop] = Gen.oneOf(true, false).map(Stop)
    val initializeGen: Gen[Initialize] = for {
      marking <- markingDataGen
      state <- processStateGen
    } yield Initialize(marking, state)

    val uninitializedGen: Gen[Uninitialized] = processIdGen.map(Uninitialized)
    val alreadyInitializedGen: Gen[AlreadyInitialized] = processIdGen.map(AlreadyInitialized)

    val initializedGen: Gen[Initialized] = for {
      marking <- markingDataGen
      state <- processStateGen
    } yield Initialized(marking, state)

    val fireTransitionGen: Gen[FireTransition] = for {
      transitionId <- transitionIdGen
      input <- transitionInputGen
      correlationId <- Gen.option(correlationIdGen)
    } yield FireTransition(transitionId, input, correlationId)

    val alreadyReceived: Gen[AlreadyReceived] = correlationIdGen.map(AlreadyReceived)

    val failureStrategyGen: Gen[ExceptionStrategy] = Gen.oneOf(
      Gen.const(ExceptionStrategy.BlockTransition),
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

    val instanceStateGen: Gen[InstanceState] = for {
      sequenceNr <- Gen.posNum[Int]
      marking <- markingDataGen
      state <- processStateGen
      jobs <- Gen.mapOf(jobStateGen.map(job => job.id -> job))
    } yield InstanceState(sequenceNr, marking, state, jobs)

    val transitionFiredGen: Gen[TransitionFired] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consumed <- markingDataGen
      produced <- markingDataGen
      newJobs <- Gen.listOf(jobIdGen).map(_.toSet)
      output <- Runtime.runtimeEventGen
    } yield TransitionFired(jobId, transitionId, correlationId, consumed, produced, newJobs, output)

    val transitionFailedGen: Gen[TransitionFailed] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consume <- markingDataGen
      input <- Runtime.runtimeEventGen
      reason <- Gen.alphaStr
      strategy <- failureStrategyGen
    } yield TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy)

    val overrideFailureGen: Gen[OverrideExceptionStrategy] = for {
      jobId <- jobIdGen
      strategy <- failureStrategyGen
    } yield OverrideExceptionStrategy(jobId, strategy)

    val invalidCommandGen: Gen[InvalidCommand] = for {
      reason <- Gen.alphaStr
    } yield InvalidCommand(reason)

    val transitionNotEnabledGen: Gen[TransitionNotEnabled] = for {
      transitionId <- transitionIdGen
      reason <- Gen.alphaStr
    } yield TransitionNotEnabled(transitionId, reason)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(getStateGen, stopGen, initializeGen, initializedGen, uninitializedGen,
      alreadyInitializedGen, fireTransitionGen, transitionFiredGen, transitionFailedGen, transitionNotEnabledGen,
      overrideFailureGen, invalidCommandGen)
  }

  object Types {

    import com.ing.baker.types._
    import com.ing.baker.types.modules.PrimitiveModuleSpec._

    val fieldNameGen: Gen[String] = Gen.alphaStr

    val primitiveTypeGen: Gen[Type] = Gen.oneOf(types.primitiveTypes.toSeq)

    val fieldTypeGen: Gen[Type] = primitiveTypeGen

    val recordTypeEntries: Gen[RecordField] = for {
      fieldName <- fieldNameGen
      fieldType <- fieldTypeGen
    } yield RecordField(fieldName, fieldType)

    val recordTypeGen: Gen[RecordType] = Gen.listOf(recordTypeEntries).map(RecordType(_))
    val listTypeGen: Gen[ListType] = primitiveTypeGen.map(ListType)
    val mapTypeGen: Gen[MapType] = primitiveTypeGen.map(MapType)
    val optionTypeGen: Gen[OptionType] = primitiveTypeGen.map(OptionType)

    val anyTypeGen: Gen[Type] = Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

    val primitiveJavaObjGen: Gen[Any] = Gen.oneOf(
      intGen, langIntegerGen, longGen, langLongGen, shortGen, langShortGen, floatGen, langFloatGen,
      doubleGen, langDoubleGen, stringGen, bigIntGen, javaBigIntGen, bigDecimalGen, javaBigDecimalGen, byteArrayGen
    )

    val primitiveValuesGen: Gen[Value] = primitiveJavaObjGen.map(PrimitiveValue)
    val listValueGen: Gen[Value] = Gen.listOf(primitiveValuesGen).map(ListValue)
    val nullValueGen: Gen[Value] = Gen.const(NullValue)

    val recordValueEntries: Gen[(String, Value)] = for {
      fieldName <- fieldNameGen
      fieldValue <- primitiveValuesGen
    } yield fieldName -> fieldValue

    val recordValueGen: Gen[Value] = Gen.mapOf(recordValueEntries).map(RecordValue)

    val anyValueGen: Gen[Value] = Gen.oneOf(primitiveValuesGen, listValueGen, recordValueGen, nullValueGen)

    val messagesGen: Gen[AnyRef] = Gen.oneOf(anyValueGen, anyTypeGen)
  }

  object BakerResponseStream {

    val eventProtocolGen: Gen[BakerResponseEventProtocol] =
      Gen.oneOf(
        ProcessInstance.transitionFiredGen.map(InstanceTransitionFired),
        ProcessInstance.transitionNotEnabledGen.map(InstanceTransitionNotEnabled),
        ProcessInstance.transitionFailedGen.map(InstanceTransitionFailed),
        ProcessInstance.alreadyReceived.map(InstanceAlreadyReceived),
        ProcessIndex.noSuchProcessGen.map(IndexNoSuchProcess),
        ProcessIndex.receivePeriodExpiredGen.map(IndexReceivePeriodExpired),
        ProcessIndex.processDeletedGen.map(IndexProcessDeleted),
        ProcessIndex.invalidEventGen.map(IndexInvalidEvent)
      )
  }
}