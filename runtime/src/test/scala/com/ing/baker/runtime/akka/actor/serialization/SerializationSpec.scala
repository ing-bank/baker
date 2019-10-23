package com.ing.baker.runtime.akka.actor.serialization

import java.util.concurrent.TimeUnit

import akka.actor.{Actor, ActorSystem, Props}
import akka.serialization.SerializationExtension
import akka.testkit.TestKit
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.petrinet.api.{Id, Marking, MultiSet}
import com.ing.baker.runtime.akka.actor.ClusterBakerActorProvider.GetShardIndex
import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProto._
import com.ing.baker.runtime.akka.actor.process_index.{ProcessIndex, ProcessIndexProtocol}
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProto._
import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManager.RecipeAdded
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProto._
import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol.GetRecipe
import com.ing.baker.runtime.akka.actor.recipe_manager.{RecipeManager, RecipeManagerProtocol}
import com.ing.baker.runtime.akka.actor.serialization.Encryption.{AESEncryption, NoEncryption}
import com.ing.baker.runtime.serialization.ProtoMap.{ctxFromProto, ctxToProto}
import com.ing.baker.runtime.common.SensoryEventStatus
import com.ing.baker.runtime.scaladsl.{EventInstance, EventMoment, RecipeInstanceState, SensoryEventResult}
import com.ing.baker.runtime.serialization.ProtoMap
import com.ing.baker.types.modules.PrimitiveModuleSpec._
import com.ing.baker.types.{Value, _}
import com.ing.baker.{AllTypeRecipe, types}
import org.scalacheck.Prop.forAll
import org.scalacheck.Test.Parameters.defaultVerbose
import org.scalacheck._
import org.scalatest.FunSuiteLike
import org.scalatest.prop.Checkers

import scala.concurrent.duration._
import scala.reflect.ClassTag
import scala.util.Success

class SerializationSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with FunSuiteLike with Checkers {

  val serializer: BakerTypedProtobufSerializer =
    SerializationExtension
      .get(system)
      .serializerByIdentity(101)
      .asInstanceOf[BakerTypedProtobufSerializer]

  import serializer.serializersProvider

  def checkFor[A <: AnyRef]: CheckFor[A] = new CheckFor[A]

  class CheckFor[A <: AnyRef]() {

    def run[P <: scalapb.GeneratedMessage with scalapb.Message[P]](implicit ev: ProtoMap[A, P], gen: Gen[A], typeTag: ClassTag[A]): Unit = {
      test(s"${typeTag.runtimeClass.getName} typed serialization") {
        check(forAll(gen) { m =>
          m === serializer.fromBinary(serializer.toBinary(m), serializer.manifest(m))
        },
          defaultVerbose.withMinSuccessfulTests(10)
        )
      }
    }
  }

  import SerializationSpec.IntermediateLanguage._
  import SerializationSpec.ProcessIndex._
  import SerializationSpec.ProcessInstance._
  import SerializationSpec.RecipeManager._
  import SerializationSpec.Runtime._
  import SerializationSpec.Types._

  checkFor[Value].run

  checkFor[Type].run

  checkFor[EventInstance].run

  checkFor[RecipeInstanceState].run

  checkFor[GetShardIndex].run

  checkFor[ProcessIndex.ActorCreated].run

  checkFor[ProcessIndex.ActorDeleted].run

  checkFor[ProcessIndex.ActorPassivated].run

  checkFor[ProcessIndex.ActorActivated].run

  checkFor[ProcessIndex.ActorMetadata].run

  test("ProcessIndexProtocol.GetIndex typed serialization") {
    val m = ProcessIndexProtocol.GetIndex
    val serialized = serializer.toBinary(m)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(m))
    deserialized === m &&
    ctxFromProto(ctxToProto(m)) === Success(m)
  }

  checkFor[ProcessIndexProtocol.Index].run

  checkFor[ProcessIndexProtocol.CreateProcess].run

  checkFor[ProcessIndexProtocol.ProcessEvent].run

  checkFor[ProcessIndexProtocol.RetryBlockedInteraction].run

  checkFor[ProcessIndexProtocol.ResolveBlockedInteraction].run

  checkFor[ProcessIndexProtocol.StopRetryingInteraction].run

  checkFor[ProcessIndexProtocol.ProcessEventResponse].run

  checkFor[ProcessIndexProtocol.ProcessEventCompletedResponse].run

  checkFor[ProcessIndexProtocol.ProcessEventReceivedResponse].run

  checkFor[ProcessIndexProtocol.GetProcessState].run

  checkFor[ProcessIndexProtocol.GetCompiledRecipe].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.ReceivePeriodExpired].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.InvalidEvent].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.RecipeInstanceDeleted].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.NoSuchRecipeInstance].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.AlreadyReceived].run

  checkFor[ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet].run

  checkFor[ProcessIndexProtocol.ProcessDeleted].run

  checkFor[ProcessIndexProtocol.NoSuchProcess].run

  checkFor[ProcessIndexProtocol.ProcessAlreadyExists].run

  checkFor[RecipeManagerProtocol.AddRecipe].run

  checkFor[RecipeManagerProtocol.AddRecipeResponse].run

  checkFor[RecipeManagerProtocol.GetRecipe].run

  checkFor[RecipeManagerProtocol.RecipeFound].run

  checkFor[RecipeManagerProtocol.NoRecipeFound].run

  checkFor[RecipeManagerProtocol.AllRecipes].run

  test("RecipeManagerProtocol.GetAllRecipes typed serialization") {
    val m = RecipeManagerProtocol.GetAllRecipes
    val serialized = serializer.toBinary(m)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(m))
    deserialized === m &&
      ctxFromProto(ctxToProto(m)) === Success(m)
  }

  checkFor[RecipeManager.RecipeAdded].run

  checkFor[ProcessInstanceProtocol.Stop].run

  test("ProcessInstanceProtocol.GetState typed serialization") {
    val m = ProcessInstanceProtocol.GetState
    val serialized = serializer.toBinary(m)
    val deserialized = serializer.fromBinary(serialized, serializer.manifest(m))
    deserialized === m &&
      ctxFromProto(ctxToProto(m)) === Success(m)
  }

  checkFor[ProcessInstanceProtocol.InstanceState].run

  checkFor[ProcessInstanceProtocol.Initialize].run

  checkFor[ProcessInstanceProtocol.Initialized].run

  checkFor[ProcessInstanceProtocol.Uninitialized].run

  checkFor[ProcessInstanceProtocol.AlreadyInitialized].run

  checkFor[ProcessInstanceProtocol.FireTransition].run

  checkFor[ProcessInstanceProtocol.OverrideExceptionStrategy].run

  checkFor[ProcessInstanceProtocol.InvalidCommand].run

  checkFor[ProcessInstanceProtocol.AlreadyReceived].run

  checkFor[ProcessInstanceProtocol.TransitionNotEnabled].run

  checkFor[ProcessInstanceProtocol.TransitionFailed].run

  checkFor[ProcessInstanceProtocol.TransitionFired].run

  checkFor[CompiledRecipe].run

  test("Encryption works for the AnyRefMapping (case class)") {

    val data = GetRecipe("test")
    val encryption = new AESEncryption(List.fill(16)("0").mkString)
    val withEncryption = serializer.serializersProvider.copy(encryption = encryption)
    val withoutEncryption = serializer.serializersProvider.copy(encryption = NoEncryption)
    val mapperEncryption = ProtoMap.anyRefMapping(withEncryption)
    val mapperNoEncryption = ProtoMap.anyRefMapping(withoutEncryption)

    val protoEn = mapperEncryption.toProto(data)
    val protoNe = mapperNoEncryption.toProto(data)

    val xEn = protoEn.data.get
    val xNe = protoNe.data.get
    assert(xEn != xNe)

    val yEn = mapperEncryption.fromProto(protoEn).get.asInstanceOf[GetRecipe]
    val yNe = mapperNoEncryption.fromProto(protoNe).get.asInstanceOf[GetRecipe]
    assert(yEn == yNe)
  }

  test("Encryption works for the AnyRefMapping (primitive value)") {

    val data = "test"
    val encryption = new AESEncryption(List.fill(16)("0").mkString)
    val withEncryption = serializer.serializersProvider.copy(encryption = encryption)
    val withoutEncryption = serializer.serializersProvider.copy(encryption = NoEncryption)
    val mapperEncryption = ProtoMap.anyRefMapping(withEncryption)
    val mapperNoEncryption = ProtoMap.anyRefMapping(withoutEncryption)

    val protoEn = mapperEncryption.toProto(data)
    val protoNe = mapperNoEncryption.toProto(data)

    val xEn = protoEn.data.get
    val xNe = protoNe.data.get
    assert(xEn != xNe)

    val yEn = mapperEncryption.fromProto(protoEn).get.asInstanceOf[String]
    val yNe = mapperNoEncryption.fromProto(protoNe).get.asInstanceOf[String]
    assert(yEn == yNe)
  }
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
  val recipeInstanceIdGen: Gen[String] = Gen.uuid.map(_.toString)
  val timestampGen: Gen[Long] = Gen.chooseNum[Long](0, Long.MaxValue)

  object IntermediateLanguage {

    val eventNameGen: Gen[String] = Gen.alphaStr
    val finiteDurationGen: Gen[FiniteDuration] = Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))
    val allTypesRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(AllTypeRecipe.recipe)

    implicit val recipeGen: Gen[CompiledRecipe] = Gen.const(allTypesRecipe)
  }

  object Runtime {

    implicit val eventNameGen: Gen[String] = Gen.alphaStr
    implicit val ingredientNameGen: Gen[String] = Gen.alphaStr
    implicit val ingredientsGen: Gen[(String, Value)] = GenUtil.tuple(ingredientNameGen, Types.anyValueGen)

    implicit val runtimeEventGen: Gen[EventInstance] = for {
      eventName <- eventNameGen
      ingredients <- Gen.listOf(ingredientsGen)
    } yield EventInstance(eventName, ingredients.toMap)

    implicit val eventMomentsGen: Gen[EventMoment] = for {
      eventName <- eventNameGen
      occurredOn <- Gen.posNum[Long]
    } yield EventMoment(eventName, occurredOn)

    implicit val processStateGen: Gen[RecipeInstanceState] = for {
      recipeInstanceId <- recipeInstanceIdGen
      ingredients <- Gen.mapOf(ingredientsGen)
      events <- Gen.listOf(eventMomentsGen)
    } yield RecipeInstanceState(recipeInstanceId, ingredients, events)

    implicit val messagesGen: Gen[AnyRef] = Gen.oneOf(runtimeEventGen, processStateGen)

    implicit val sensoryEventResultGen: Gen[SensoryEventResult] = for {
      status <- Gen.oneOf(
        SensoryEventStatus.AlreadyReceived,
        SensoryEventStatus.Completed,
        SensoryEventStatus.FiringLimitMet,
        SensoryEventStatus.RecipeInstanceDeleted,
        SensoryEventStatus.Received,
        SensoryEventStatus.ReceivePeriodExpired)
      events <- Gen.listOf(eventNameGen)
      ingredients <- Gen.listOf(ingredientsGen)
    } yield SensoryEventResult(status, events, ingredients.toMap)
  }

  object RecipeManager {

    import IntermediateLanguage._
    import com.ing.baker.runtime.akka.actor.recipe_manager.RecipeManagerProtocol._

    implicit val addRecipeGen: Gen[AddRecipe] = recipeGen.map(AddRecipe)
    implicit val getRecipeGen: Gen[GetRecipe] = recipeIdGen.map(GetRecipe)
    implicit val recipeFoundGen: Gen[RecipeFound] = for {
      compiledRecipe <- IntermediateLanguage.recipeGen
      timestamp <- timestampGen
    } yield RecipeFound(compiledRecipe, timestamp)


    implicit val noRecipeFoundGen: Gen[NoRecipeFound] = recipeIdGen.map(NoRecipeFound)
    implicit val addRecipeResponseGen: Gen[AddRecipeResponse] = recipeIdGen.map(AddRecipeResponse)
    implicit val getAllRecipesGen: Gen[GetAllRecipes.type] = Gen.const(GetAllRecipes)

    implicit val recipeEntriesGen: Gen[(String, CompiledRecipe)] = GenUtil.tuple(recipeIdGen, recipeGen)

    implicit val recipeInformationGen: Gen[RecipeInformation] = for {
      compiledRecipe <- recipeGen
      timestamp <- timestampGen
    } yield RecipeInformation(compiledRecipe, timestamp)

    implicit val allRecipesGen: Gen[AllRecipes] = Gen.listOf(recipeInformationGen).map(AllRecipes(_))

    implicit val messagesGen: Gen[AnyRef] = Gen.oneOf(
      addRecipeGen, getRecipeGen, recipeFoundGen, noRecipeFoundGen, addRecipeResponseGen, getAllRecipesGen, allRecipesGen
    )

    implicit val recipeAddedGen: Gen[RecipeAdded] =
      for {
        timestamp <- Gen.chooseNum(0l, 20000l)
        recipe <- recipeGen
      } yield RecipeAdded(recipe, timestamp)
  }

  object ProcessIndex {

    import com.ing.baker.runtime.akka.actor.process_index.ProcessIndex._
    import com.ing.baker.runtime.akka.actor.process_index.ProcessIndexProtocol._

    implicit val processStatusGen: Gen[ProcessStatus] = Gen.oneOf(Active, Deleted)
    implicit val createdTimeGen: Gen[Long] = Gen.chooseNum[Long](0, Long.MaxValue)

    implicit val actorMetadataGen: Gen[ActorMetadata] = for {
      recipeId <- recipeIdGen
      recipeInstanceId <- recipeInstanceIdGen
      createdTime <- createdTimeGen
      status <- processStatusGen
    } yield ActorMetadata(recipeId, recipeInstanceId, createdTime, status)

    implicit val getIndexGen: Gen[ProcessIndexProtocol.GetIndex.type] = Gen.const(GetIndex)
    implicit val indexGen: Gen[Index] = Gen.listOf(actorMetadataGen).map(Index(_))

    implicit val createProcessGen: Gen[CreateProcess] = for {
      recipeId <- recipeIdGen
      recipeInstanceId <- recipeInstanceIdGen
    } yield CreateProcess(recipeId, recipeInstanceId)

    class SimpleActor extends Actor {
      override def receive: Receive = { case _ => () }
    }

    val waitForRetriesGen = Gen.oneOf(true, false)

    implicit def processEventGen(implicit system: ActorSystem): Gen[ProcessEvent] = for {
      recipeInstanceId <- recipeInstanceIdGen
      event <- Runtime.runtimeEventGen
      correlationId <- Gen.option(recipeInstanceIdGen)
      timeout <- Gen.posNum[Long].map(millis => FiniteDuration(millis, TimeUnit.MILLISECONDS))
      reaction <- Gen.oneOf(
        Gen.const(FireSensoryEventReaction.NotifyWhenReceived),
        waitForRetriesGen.map(FireSensoryEventReaction.NotifyWhenCompleted.apply),
        for {
          waitForRetries <- waitForRetriesGen
          receiver = system.actorOf(Props(new SimpleActor))
        } yield FireSensoryEventReaction.NotifyBoth(waitForRetries, receiver),
        for {
          waitForRetries <- Gen.oneOf(true, false)
          onEvent <- Gen.alphaStr
        } yield FireSensoryEventReaction.NotifyOnEvent(waitForRetries, onEvent)
      )
    } yield ProcessEvent(recipeInstanceId, event, correlationId, timeout, reaction)

    implicit val getProcessStateGen: Gen[GetProcessState] = recipeInstanceIdGen.map(GetProcessState)
    implicit val getCompiledRecipeGen: Gen[GetCompiledRecipe] = recipeInstanceIdGen.map(GetCompiledRecipe)

    implicit val processDeletedGen: Gen[ProcessDeleted] = recipeInstanceIdGen.map(ProcessDeleted)
    implicit val noSuchProcessGen: Gen[NoSuchProcess] = recipeInstanceIdGen.map(NoSuchProcess)
    implicit val processAlreadyExistsGen: Gen[ProcessAlreadyExists] = recipeInstanceIdGen.map(ProcessAlreadyExists)

    implicit val retryBlockedInteractionGen: Gen[RetryBlockedInteraction] = for {
      recipeInstanceId <- recipeInstanceIdGen
      interactionName <- Gen.alphaStr
    } yield RetryBlockedInteraction(recipeInstanceId, interactionName)

    implicit val stopRetryingInteractionGen: Gen[StopRetryingInteraction] = for {
      recipeInstanceId <- recipeInstanceIdGen
      interactionName <- Gen.alphaStr
    } yield StopRetryingInteraction(recipeInstanceId, interactionName)

    val sensoryEventStatusGen: Gen[SensoryEventStatus] = Gen.oneOf(
      SensoryEventStatus.AlreadyReceived ,
      SensoryEventStatus.Completed,
      SensoryEventStatus.FiringLimitMet,
      SensoryEventStatus.Received,
      SensoryEventStatus.ReceivePeriodExpired,
      SensoryEventStatus.RecipeInstanceDeleted
    )

    val eventResultGen: Gen[SensoryEventResult] = for {
        status <- sensoryEventStatusGen
        events <- Gen.listOf(Gen.alphaStr)
        ingredients <- Gen.listOf(Runtime.ingredientsGen)
    } yield SensoryEventResult(status, events, ingredients.toMap)

    implicit val processEventResponse: Gen[ProcessEventResponse] = for {
      recipeInstanceId <- Gen.alphaStr
    } yield ProcessEventResponse(recipeInstanceId)

    implicit val processEventCompletedResponse: Gen[ProcessEventCompletedResponse] = for {
      result <- eventResultGen
    } yield ProcessEventCompletedResponse(result)

    implicit val processEventReceivedResponse: Gen[ProcessEventReceivedResponse] = for {
      status <- sensoryEventStatusGen
    } yield ProcessEventReceivedResponse(status)

    /*
    def messagesGen(system: ActorSystem): Gen[AnyRef] = Gen.oneOf(getIndexGen, indexGen, createProcessGen, processEventGen(system),
      getProcessStateGen, getCompiledRecipeGen, receivePeriodExpiredGen, invalidEventGen, processDeletedGen,
      noSuchProcessGen, processAlreadyExistsGen, retryBlockedInteractionGen, resolveBlockedInteraction, stopRetryingInteractionGen)
     */


    implicit val identifierGen: Gen[String] = Gen.alphaNumStr

    implicit val timestampGen: Gen[Long] = Gen.chooseNum(100000l, 1000000l)

    implicit val getShardIndexGen: Gen[GetShardIndex] =
      identifierGen.map(GetShardIndex)

    implicit val actorCreatedGen: Gen[ActorCreated] =
      for {
        recipeId <- identifierGen
        recipeInstanceId <- identifierGen
        timestamp <- timestampGen
      } yield ActorCreated(recipeId, recipeInstanceId, timestamp)

    implicit val actorActivatedGen: Gen[ActorActivated] =
      identifierGen.map(ActorActivated)

    implicit val actorPassivatedGen: Gen[ActorPassivated] =
      identifierGen.map(ActorPassivated)

    implicit val actorDeletedGen: Gen[ActorDeleted] =
      identifierGen.map(ActorDeleted)

    implicit val resolveBlockedInteractionGen: Gen[ResolveBlockedInteraction] =
      for {
        recipeId <- identifierGen
        recipeInstanceId <- identifierGen
        event <- Runtime.runtimeEventGen
      } yield ResolveBlockedInteraction(recipeId, recipeInstanceId, event)

    implicit val receivePeriodExpiredGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.ReceivePeriodExpired] =
      for {
        recipeInstanceId <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.ReceivePeriodExpired(recipeInstanceId)

    implicit val invalidEventGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.InvalidEvent] =
      for {
        recipeInstanceId <- Gen.alphaStr
        message <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.InvalidEvent(recipeInstanceId, message)

    implicit val recipeInstanceDeletedGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.RecipeInstanceDeleted] =
      for {
        recipeInstanceId <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.RecipeInstanceDeleted(recipeInstanceId)

    implicit val noSuchRecipeInstanceGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.NoSuchRecipeInstance] =
      for {
        recipeInstanceId <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.NoSuchRecipeInstance(recipeInstanceId)

    implicit val alreadyReceivedGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.AlreadyReceived] =
      for {
        recipeInstanceId <- Gen.alphaStr
        correlationId <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.AlreadyReceived(recipeInstanceId, correlationId)

    implicit val firingLimitMetGen: Gen[ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet] =
      for {
        recipeInstanceId <- Gen.alphaStr
      } yield ProcessIndexProtocol.FireSensoryEventRejection.FiringLimitMet(recipeInstanceId)

  }

  object ProcessInstance {

    import com.ing.baker.runtime.akka.actor.process_instance.ProcessInstanceProtocol._

    implicit val transitionIdGen: Gen[Id] = Gen.posNum[Long]
    implicit val placeIdGen: Gen[Id] = Gen.posNum[Long]
    implicit val jobIdGen: Gen[Id] = Gen.posNum[Long]
    implicit val tokenDataGen: Gen[String] = Gen.alphaStr
    implicit val correlationIdGen: Gen[String] = Gen.uuid.map(_.toString)

    implicit val multiSetGen: Gen[MultiSet[Any]] = Gen.nonEmptyMap[Any, Int](GenUtil.tuple(tokenDataGen, Gen.posNum[Int]))
    implicit val markingDataGen: Gen[Marking[Id]] = Gen.mapOf(GenUtil.tuple(placeIdGen, multiSetGen))

    implicit val getStateGen: Gen[ProcessInstanceProtocol.GetState.type] = Gen.const(GetState)
    implicit val stopGen: Gen[Stop] = Gen.oneOf(true, false).map(Stop)
    implicit val initializeGen: Gen[Initialize] = for {
      marking <- markingDataGen
      state <- Runtime.processStateGen
    } yield Initialize(marking, state)

    implicit val uninitializedGen: Gen[Uninitialized] = recipeInstanceIdGen.map(Uninitialized)
    implicit val alreadyInitializedGen: Gen[AlreadyInitialized] = recipeInstanceIdGen.map(AlreadyInitialized)

    implicit val initializedGen: Gen[Initialized] = for {
      marking <- markingDataGen
      state <- Runtime.processStateGen
    } yield Initialized(marking, state)

    implicit val fireTransitionGen: Gen[FireTransition] = for {
      transitionId <- transitionIdGen
      input <- Runtime.runtimeEventGen
      correlationId <- Gen.option(correlationIdGen)
    } yield FireTransition(transitionId, input, correlationId)

    implicit val alreadyReceived: Gen[ProcessInstanceProtocol.AlreadyReceived] =
      correlationIdGen.map(ProcessInstanceProtocol.AlreadyReceived)

    implicit val failureStrategyGen: Gen[ExceptionStrategy] = Gen.oneOf(
      Gen.const(ExceptionStrategy.BlockTransition),
      Gen.posNum[Long].map(delay => ExceptionStrategy.RetryWithDelay(delay)),
      for {
        marking <- markingDataGen
        output <- Runtime.runtimeEventGen
      } yield ExceptionStrategy.Continue(marking, output)
    )

    implicit val exceptionStateGen: Gen[ExceptionState] = for {
      failureCount <- Gen.posNum[Int]
      failureReason <- Gen.alphaStr
      failureStrategy <- failureStrategyGen
    } yield ExceptionState(failureCount, failureReason, failureStrategy)

    implicit val jobStateGen: Gen[JobState] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      consumed <- markingDataGen
      input <- Runtime.runtimeEventGen
      exceptionState <- Gen.option(exceptionStateGen)
    } yield JobState(jobId, transitionId, consumed, input, exceptionState)

    implicit val instanceStateGen: Gen[InstanceState] = for {
      sequenceNr <- Gen.posNum[Int]
      marking <- markingDataGen
      state <- Runtime.processStateGen
      jobs <- Gen.mapOf(jobStateGen.map(job => job.id -> job))
    } yield InstanceState(sequenceNr, marking, state, jobs)

    implicit val transitionFiredGen: Gen[TransitionFired] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consumed <- markingDataGen
      produced <- markingDataGen
      newJobs <- Gen.listOf(jobIdGen).map(_.toSet)
      output <- Runtime.runtimeEventGen
    } yield TransitionFired(jobId, transitionId, correlationId, consumed, produced, newJobs, output)

    implicit val transitionFailedGen: Gen[TransitionFailed] = for {
      jobId <- jobIdGen
      transitionId <- transitionIdGen
      correlationId <- Gen.option(correlationIdGen)
      consume <- markingDataGen
      input <- Runtime.runtimeEventGen
      reason <- Gen.alphaStr
      strategy <- failureStrategyGen
    } yield TransitionFailed(jobId, transitionId, correlationId, consume, input, reason, strategy)

    implicit val overrideFailureGen: Gen[OverrideExceptionStrategy] = for {
      jobId <- jobIdGen
      strategy <- failureStrategyGen
    } yield OverrideExceptionStrategy(jobId, strategy)

    implicit val invalidCommandGen: Gen[InvalidCommand] = for {
      reason <- Gen.alphaStr
    } yield InvalidCommand(reason)

    implicit val transitionNotEnabledGen: Gen[TransitionNotEnabled] = for {
      transitionId <- transitionIdGen
      reason <- Gen.alphaStr
    } yield TransitionNotEnabled(transitionId, reason)

    implicit val messagesGen: Gen[AnyRef] = Gen.oneOf(getStateGen, stopGen, initializeGen, initializedGen, uninitializedGen,
      alreadyInitializedGen, fireTransitionGen, transitionFiredGen, transitionFailedGen, transitionNotEnabledGen,
      overrideFailureGen, invalidCommandGen)
  }

  object Types {

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

    implicit val anyTypeGen: Gen[Type] = Gen.oneOf(primitiveTypeGen, recordTypeGen, listTypeGen, mapTypeGen, optionTypeGen)

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

    implicit val anyValueGen: Gen[Value] = Gen.oneOf(primitiveValuesGen, listValueGen, recordValueGen, nullValueGen)
  }

}