package com.ing.baker.runtime.akka

import java.net.MalformedURLException
import java.util.concurrent.TimeUnit
import java.util.{Optional, UUID}
import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.{TestDuration, TestKit, TestProbe}
import cats.effect.IO
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.FireEventAfterFailure
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Interaction, Recipe, CheckPointEvent}
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.BakerException._
import com.ing.baker.runtime.common.RecipeInstanceState.RecipeInstanceMetaDataName
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance, InteractionInstanceInput, RecipeEventMetadata}
import com.ing.baker.types.{CharArray, Int32, PrimitiveValue, Value}
import com.typesafe.config.{Config, ConfigFactory}
import io.prometheus.client.CollectorRegistry
import org.mockito.ArgumentMatchers.{any, anyString, argThat, eq => mockitoEq}
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock
import org.mockito.stubbing.Answer
import org.slf4j.LoggerFactory

import scala.collection.immutable.Seq
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.language.postfixOps

case class SomeNotDefinedEvent(name: String)

class BakerExecutionSpec extends BakerRuntimeTestBase {

  override def actorSystemName = "BakerExecutionSpec"

  before {
    resetMocks()
    setupMockResponse()
    CollectorRegistry.defaultRegistry.clear()
    //clean the in-memory journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

  "The baker setup" should {
    "use akka service discovery" in {
      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |akka.actor.provider = "cluster"
          |
          |baker.actor.provider = "cluster-sharded"
          |
          |baker.recipe-manager-type = "actor"
          |
          |akka.management {
          |  cluster.bootstrap {
          |    contact-point-discovery {
          |      # For the kubernetes API this value is substributed into the %s in pod-label-selector
          |      service-name = "baker"
          |
          |      # pick the discovery method you'd like to use:
          |      discovery-method = kubernetes-api
          |    }
          |  }
          |}
          |""".stripMargin).withFallback(ConfigFactory.load())
      val setupActorSystem = ActorSystem("setup-actor-system", config)
      for {
        exception <- Future.successful {
          intercept[IllegalArgumentException] {
            AkkaBaker(config, setupActorSystem, CachingInteractionManager())
          }
        }
        _ <- setupActorSystem.terminate()
      } yield assert(exception.getMessage contains "akka.discovery.kubernetes-api.class must point to a FQN of a `akka.discovery.ServiceDiscovery` implementation")
    }


    "use akka seed node list" in {
      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |akka.actor.provider = "cluster"
          |
          |baker.actor.provider = "cluster-sharded"
          |
          |baker.cluster.seed-nodes = ["wrong-address"]
          |
          |""".stripMargin).withFallback(ConfigFactory.load())
      val setupActorSystem = ActorSystem("setup-actor-system", config)
      for {
        exception <- Future.successful {
          intercept[MalformedURLException](AkkaBaker(config, setupActorSystem, CachingInteractionManager()))
        }
        _ <- setupActorSystem.terminate()
      } yield assert(exception.getMessage contains "wrong-address")
    }

    "fail when no seed nodes or boostrap cluster configuration is set" in {
      val config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |akka.actor.provider = "cluster"
          |
          |baker.actor.provider = "cluster-sharded"
          |
          |baker.recipe-manager-type = "actor"
          |
          |""".stripMargin).withFallback(ConfigFactory.load())
      val setupActorSystem = ActorSystem("setup-actor-system", config)
      for {
        exception <- Future.successful {
          intercept[IllegalArgumentException](AkkaBaker(config, setupActorSystem, CachingInteractionManager()))
        }
        _ <- setupActorSystem.terminate()
      } yield assert(exception.getMessage contains "No default service discovery implementation configured in `akka.discovery.method`")
    }
  }

  "The Baker execution engine" should {

    "bake a process successfully if baking for the first time" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
      } yield succeed
    }

    "bake a process successfully if baking for the first time with MetaData" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id, Map("key" -> "value"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetaDataName).asMap(classOf[String], classOf[String])
      } yield
        assert(metaData.containsKey("key") && metaData.get("key") == "value")
    }

    "bake and terminate baker successfully" in {
      val terminationActorSystem = ActorSystem("termination-actor-system")
      for {
        (baker, recipeId) <- setupBakerWithRecipe("FirstTimeBaking")(terminationActorSystem)
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.gracefulShutdown()
        _ <- terminationActorSystem.whenTerminated
      } yield succeed
    }

    "throw an ProcessAlreadyExistsException if baking a process with the same identifier twice" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("DuplicateIdentifierRecipe")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- recoverToSucceededIf[ProcessAlreadyExistsException] {
          baker.bake(recipeId, id)
        }
      } yield succeed
    }

    "allows adding metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataOne")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value"))
        _ <- baker.addMetaData(id, Map.apply[String, String]("key2" -> "value2"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetaDataName).asMap(classOf[String], classOf[String])
      } yield assert(
        metaData.containsKey("key") && metaData.get("key") == "value" &&
        metaData.containsKey("key2") && metaData.get("key2") == "value2")
    }

    "allows updating metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataTwo")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value"))
        _ <- baker.addMetaData(id, Map.apply[String, String]("key" -> "value2"))
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetaDataName).asMap(classOf[String], classOf[String])
      } yield
        assert(
          metaData.containsKey("key") && metaData.get("key") == "value2")
    }

    "allows empty metadata to an RecipeInstance" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("MetaDataFour")
        id = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, id)
        _ <- baker.addMetaData(id, Map.empty)
        ingredients: Map[String, Value] <- baker.getIngredients(id)
        metaData = ingredients(RecipeInstanceMetaDataName).asMap(classOf[String], classOf[String])
      } yield
        assert(
          metaData.size() == 0)
    }

    "retry a blocked interaction" in {
      val recipe =
        Recipe("RetryBlockedInteractionRecipe")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException("Expected test failure"))
          .thenReturn(Future.successful(InteractionOneSuccessful("success!")))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.retryInteraction(recipeInstanceId, interactionOne.name)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    "retry a blocked interaction after it had the FireEvent retry strategy" in {
      val recipe =
        Recipe("RetryBlockedInteractionRecipe")
          .withInteraction(interactionOne
            .withFailureStrategy(InteractionFailureStrategy.FireEventAfterFailure(Some("interactionOneSuccessful"))))
          .withSensoryEvent(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        _ = when(testInteractionOneMock.apply(anyString(), anyString()))
          .thenThrow(new RuntimeException("Expected test failure"))
          .thenReturn(Future.successful(InteractionOneSuccessful("success!")))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        state0 <- baker.getRecipeInstanceState(recipeInstanceId)
        _ = state0.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue)
        _ <- baker.retryInteraction(recipeInstanceId, interactionOne.name)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield state.ingredients shouldBe
        ingredientMap(
          "initialIngredient" -> initialIngredientValue,
          "interactionOneOriginalIngredient" -> "success!")
    }

    "be able to return" when {
      "all occurred events" in {
        for {
          (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          //Handle first event
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
          //Check if both the new event and the events occurred in the past are in the eventsList
          state0 <- baker.getRecipeInstanceState(recipeInstanceId)
          _ = state0.eventNames should contain only(
            "InitialEvent",
            "SieveInteractionSuccessful",
            "EventFromInteractionTwo",
            "InteractionOneSuccessful",
            "InteractionThreeSuccessful"
          )
          //Execute another event
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
          //Check if both the new event and the events occurred in the past are in the eventsList
          state <- baker.getRecipeInstanceState(recipeInstanceId)
        } yield state.eventNames should contain only(
          "InitialEvent",
          "EventFromInteractionTwo",
          "SecondEvent",
          "InteractionOneSuccessful",
          "SieveInteractionSuccessful",
          "InteractionThreeSuccessful",
          "InteractionFourSuccessful"
        )
      }

      "an index of all processes in cluster mode" in {
        val journalId = java.util.UUID.randomUUID().toString
        val indexTestSystem = ActorSystem("indexTest", clusterLevelDBConfig(
          actorSystemName = "indexTest",
          port = 3005,
          journalPath = s"target/journal-$journalId",
          snapshotsPath = s"target/snapshots-$journalId"))
        val nrOfProcesses = 200

        for {
          (baker, recipeId) <- setupBakerWithRecipe("IndexTestCluster")(indexTestSystem)
          recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
          _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
          index <- baker.getAllRecipeInstancesMetadata
        } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
      }

      "an index of all processes in local/in-memory mode" in {

        val nrOfProcesses = 200

        for {
          (baker, recipeId) <- setupBakerWithRecipe("IndexTestLocal")
          recipeInstanceIds = (0 to nrOfProcesses).map(_ => java.util.UUID.randomUUID().toString).toSet
          _ <- Future.traverse(recipeInstanceIds)(baker.bake(recipeId, _))
          index <- baker.getAllRecipeInstancesMetadata
        } yield index.map(_.recipeInstanceId) shouldBe recipeInstanceIds
      }
    }

    //Only works if persistence actors are used (think cassandra)
    "recover the state of a process from a persistence store" in {
      val system1 = ActorSystem("persistenceTest1", localLevelDBConfig("persistenceTest1"))
      val recoveryRecipeName = "RecoveryRecipe"
      val recipeInstanceId = UUID.randomUUID().toString

      val compiledRecipe = RecipeCompiler.compileRecipe(getRecipe(recoveryRecipeName))

      val first = (for {
        baker1 <- setupBakerWithNoRecipe()(system1)
        recipeId <- baker1.addRecipe(RecipeRecord.of(compiledRecipe))
        _ <- baker1.bake(recipeId, recipeInstanceId)
        _ <- baker1.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        _ <- baker1.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        state <- baker1.getRecipeInstanceState(recipeInstanceId)
        _ = state.ingredients shouldBe finalState
      } yield recipeId).transform(
        { a => TestKit.shutdownActorSystem(system1); a },
        { a => TestKit.shutdownActorSystem(system1); a }
      )

      def second(recipeId: String) = {
        val system2 = ActorSystem("persistenceTest2", localLevelDBConfig("persistenceTest2"))
        (for {
          baker2 <- setupBakerWithNoRecipe()(system2)
          recipeId <- baker2.addRecipe(RecipeRecord.of(compiledRecipe))
          state <- baker2.getRecipeInstanceState(recipeInstanceId)
          recipe <- baker2.getRecipe(recipeId)
          recipeId0 <- baker2.addRecipe(RecipeRecord.of(compiledRecipe))
        } yield {
          state.ingredients shouldBe finalState
          recipe.compiledRecipe shouldBe compiledRecipe
          recipeId0 shouldBe recipeId
        }).transform(
          { a => TestKit.shutdownActorSystem(system2); a },
          { a => TestKit.shutdownActorSystem(system2); a }
        )
      }

      first.flatMap(second)
    }

    "acknowledge the first event, not wait on the rest" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("NotWaitForTheRest")
        interaction2Delay = 2000
        _ = when(testInteractionTwoMock.apply(anyString())).thenAnswer {
          _: InvocationOnMock => {
            Thread.sleep(interaction2Delay)
            interactionTwoEventValue
          }
        }
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    "acknowledge the first and final event while rest processing failed" in {
      for {
        (baker, recipeId) <- setupBakerWithRecipe("AcknowledgeThefirst")
        _ = when(testInteractionTwoMock.apply(anyString()))
          .thenThrow(new RuntimeException("Unknown Exception.")) // This interaction is not retried and blocks the process
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        response = baker.fireEvent(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
        received <- response.resolveWhenReceived
        _ = received shouldBe SensoryEventStatus.Received
        completed <- response.resolveWhenCompleted
        // The process is completed because it is in a BLOCKED state
        _ = completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
      } yield succeed
    }

    "bind multi transitions correctly even if ingredient name overlaps" in {
      //This test is part of the ExecutionSpec and not the Compiler spec because the only correct way to validate
      //for this test is to check if Baker calls the mocks.
      //If there is a easy way to validate the created petrinet by the compiler it should be moved to the compiler spec.
      for {
        (baker, recipeId) <- setupBakerWithRecipe("OverlappingMultiIngredients")

        // It is helpful to check the recipe visualization if this test fails
        //      println(baker.compiledRecipe.getRecipeVisualization)

        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, initialIngredientValue)
        _ = verify(testInteractionTwoMock, times(1)).apply(initialIngredientValue)
        _ = verifyNoMoreInteractions(testInteractionFiveMock, testInteractionSixMock)
      } yield succeed
    }

    "be able to use the same ingredient multiple times as input parameter for an interaction" in {
      val recipe: Recipe =
        Recipe("sameIngredientMultipleTime")
          .withInteractions(
            interactionOne,
            interactionThree
              .withOverriddenIngredientName("interactionOneIngredient", "interactionOneOriginalIngredient")
              .withOverriddenIngredientName("interactionTwoIngredient", "interactionOneOriginalIngredient"))
          .withSensoryEvents(initialEvent)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        recipeInstanceId = UUID.randomUUID().toString

        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))

        _ = verify(testInteractionOneMock, times(1)).apply(recipeInstanceId.toString, initialIngredientValue)
        _ = verify(testInteractionThreeMock, times(1)).apply(interactionOneIngredientValue, interactionOneIngredientValue)
      } yield succeed
    }

    "reject sensory events after a specified receive period" in {

      val receivePeriod: FiniteDuration = 100 milliseconds

      val recipe: Recipe =
        Recipe("eventReceiveExpirationRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- Future {
          Thread.sleep(receivePeriod.toMillis + 100)
        }
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
        _ = completed.sensoryEventStatus shouldBe SensoryEventStatus.ReceivePeriodExpired
      } yield succeed
    }

    "accept sensory events before a specified receive period" in {

      val receivePeriod: FiniteDuration = 10 seconds

      val recipe: Recipe =
        Recipe("eventReceiveInTimeRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withEventReceivePeriod(receivePeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        completed <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("")))
      } yield completed.sensoryEventStatus shouldBe SensoryEventStatus.Completed
    }

    "be able to visualize events that have been fired" in {
      //This test only checks if the graphviz is different, not that the outcome is correct
      for {
        (baker, recipeId) <- setupBakerWithRecipe("CheckEventRecipe")
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        noEventsGraph = baker.getVisualState(recipeInstanceId)
        //System.out.println(noEventsGraph)
        //Handle first event
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent("initialIngredient")))
        firstEventGraph <- baker.getVisualState(recipeInstanceId)
        //System.out.println(firstEventGraph)
        _ = noEventsGraph should not be firstEventGraph
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(SecondEvent()))
        secondEventGraph <- baker.getVisualState(recipeInstanceId)
        //System.out.println(secondEventGraph)
        _ = firstEventGraph should not be secondEventGraph
      } yield succeed
    }

    "properly handle a retention period" in {

      val retentionPeriod = 2 seconds

      val recipe: Recipe =
        Recipe("RetentionPeriodRecipe")
          .withSensoryEvents(initialEvent)
          .withInteractions(interactionOne)
          .withRetentionPeriod(retentionPeriod)

      for {
        (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        //Should not fail
        _ <- baker.getRecipeInstanceState(recipeInstanceId)
        _ <- Future {
          Thread.sleep(FiniteDuration(retentionPeriod.toMillis + 1000, TimeUnit.MILLISECONDS).dilated.toMillis)
        }
        //Should fail
        _ <- recoverToSucceededIf[ProcessDeletedException] {
          baker.getRecipeInstanceState(recipeInstanceId)
        }
      } yield succeed
    }

    "block interaction and log error message" when {
      "a null ingredient is provided directly by an interaction" in {
        val recipe =
          Recipe("NullIngredientRecipe")
            .withInteraction(interactionOne)
            .withSensoryEvent(initialEvent)

        for {
          (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
          _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(null)
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
          _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
          state <- baker.getRecipeInstanceState(recipeInstanceId)
          _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
        } yield succeed
      }

      "a null ingredient is provided by an event provided by an interaction" in {
        val recipe =
          Recipe("NullIngredientFromEventRecipe")
            .withInteraction(interactionTwo
              .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"))
            .withSensoryEvent(initialEvent)

        for {
          (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
          _ = when(testInteractionTwoMock.apply(anyString())).thenReturn(EventFromInteractionTwo(null))
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
          _ = verify(testInteractionTwoMock).apply("initialIngredient")
          state <- baker.getRecipeInstanceState(recipeInstanceId)
          _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue)
        } yield succeed
      }
    }

    "fire checkpoint-event" in {

        val recipe =
          Recipe("CheckpointEvent")
            .withInteraction(interactionOne)
            .withSensoryEvent(initialEvent)
            .withCheckpointEvent(CheckPointEvent("Success")
              .withRequiredEvent(initialEvent)
              .withRequiredEvent(interactionOneSuccessful))

        for {
          (baker, recipeId) <- setupBakerWithRecipe(recipe, mockImplementations)
          _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful("Hello")))
          recipeInstanceId = UUID.randomUUID().toString
          _ <- baker.bake(recipeId, recipeInstanceId)
          _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(InitialEvent(initialIngredientValue)))
          _ = verify(testInteractionOneMock).apply(recipeInstanceId, "initialIngredient")
          state <- baker.getRecipeInstanceState(recipeInstanceId)
          _ = state.ingredients shouldBe ingredientMap("initialIngredient" -> initialIngredientValue, "interactionOneOriginalIngredient" -> "Hello")
          _ = state.eventNames shouldBe Seq("InitialEvent", "InteractionOneSuccessful", "Success")
        } yield succeed

    }
  }
}
