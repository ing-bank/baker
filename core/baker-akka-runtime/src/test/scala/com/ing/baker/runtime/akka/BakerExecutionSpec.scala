package com.ing.baker.runtime.akka

import akka.actor.ActorSystem
import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.{TestKit, TestProbe}
import com.ing.baker._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.scaladsl.Recipe
import com.ing.baker.runtime.common._
import com.ing.baker.runtime.core.util.CachingInteractionManager
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.runtime.testkit.BakerExecutionSpecLike
import com.typesafe.config.{Config, ConfigFactory}
import io.prometheus.client.CollectorRegistry
import org.mockito.ArgumentMatchers.{any, anyString}
import org.mockito.Mockito._
import org.mockito.invocation.InvocationOnMock

import java.net.MalformedURLException
import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.language.postfixOps

class BakerExecutionSpec extends BakerAkkaRuntimeTestBase with BakerExecutionSpecLike {

  override def actorSystemName = "BakerExecutionSpec"

  override protected def stubInteractionOneWithDelay(interactionDelay: FiniteDuration): Unit = {
    when(testInteractionOneMock.apply(anyString(), anyString())).thenAnswer((_: InvocationOnMock) => {
      Future {
        Thread.sleep(interactionDelay.toMillis)
        InteractionOneSuccessful(interactionOneIngredientValue)
      }(defaultActorSystem.dispatcher)
    })
  }

  override protected def awaitEventShouldTimeout(baker: Baker, recipeInstanceId: String, eventName: String, timeout: FiniteDuration): Future[Any] =
    baker.asInstanceOf[AkkaBaker].awaitEvent(recipeInstanceId, eventName, timeout)

  override def whenTerminated(): Future[Unit] = defaultActorSystem.whenTerminated.map(_ => ())

  before {
    TestKit.shutdownActorSystem(defaultActorSystem)
    defaultActorSystem = ActorSystem(UUID.randomUUID().toString)
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
    "execute an interaction when its ingredient is provided in cluster" in {
      val recipe =
        Recipe("IngredientProvidedRecipeCluster")
          .withInteraction(interactionOne)
          .withSensoryEvent(initialEvent)

      val config: Config = ConfigFactory.parseString(
        """
          |include "baker.conf"
          |
          |akka {
          |  actor {
          |    provider = "cluster"
          |  }
          |  remote {
          |    log-remote-lifecycle-events = off
          |    netty.tcp {
          |      hostname = "127.0.0.1"
          |      port = 2555
          |    }
          |  }
          |
          |  cluster {
          |    seed-nodes = ["akka://remoteTest@127.0.0.1:2555"]
          |    auto-down-unreachable-after = 10s
          |  }
          |}
        """.stripMargin).withFallback(ConfigFactory.load())

      val baker = AkkaBaker(config, ActorSystem.apply("remoteTest", config), CachingInteractionManager(mockImplementations))

      for {
        recipeId <- baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe)))
        _ = when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(EventInstance.unsafeFrom(InitialEvent(initialIngredientValue))))
        _ = verify(testInteractionOneMock).apply(recipeInstanceId.toString, "initialIngredient")
        state <- baker.getRecipeInstanceState(recipeInstanceId)
      } yield
        state.ingredients shouldBe
          ingredientMap(
            "initialIngredient" -> initialIngredientValue,
            "interactionOneOriginalIngredient" -> interactionOneIngredientValue)
    }

    "backwards compatibility in serialization of case class ingredients, THIS TEST IS BROKEN FIX ME!" ignore {

      val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))

      // These tests are broken on windows, requires some investigation
      // Still broken, cause unknown, might be that we stopped being backwards compatible or data got corrupted
      if (isWindows) Future.successful {
        println(Console.YELLOW + "WARNING: You are testing on a Windows system, notice that this test is not working and needs to eventually be addressed")
        succeed
      } else {
        import better.files._

        /**
         * This is the path where the original messages where persisted
         *
         * For the test they are copied to a temporary directory in /target
         *
         * !!! If you want to create a new test case the following flag to true
         */
        val createNewCase: Boolean = false

        val journalPath = "src/test/resources/persisted-messages" + (if (isWindows) "-windows" else "")
        val journalDir = File(journalPath)

        val testPath = if (createNewCase) journalPath else "target/backwardsCompatibilityOfEvents"
        val testDir = File(testPath).createDirectoryIfNotExists()

        if (!createNewCase) {
          testDir.delete()
          testDir.createDirectory()
          journalDir./("journal").copyToDirectory(testDir)
        }

        val config = clusterLevelDBConfig(
          "backwardsCompatibilityOfEvents",
          3004,
          10 seconds,
          s"$testPath/journal",
          s"$testPath/snapshots")

        val actorSystem = ActorSystem("backwardsCompatibilityOfEvents", config)

        import com.ing.baker.Webshop._

        val recipe = Webshop.webshopRecipe

        // test data
        val customerInfo = new Webshop.CustomerInfo("klaas", "straat", "email")
        val recipeInstanceId = "backwards-compatible-process"
        val order = "123"
        val trackingId = "trackingId"
        val goods = "some goods"

        // mocks
        val shipGoodsMock: ShipGoods = mock[Webshop.ShipGoods]
        val sendInvoiceMock: SendInvoice = mock[Webshop.SendInvoice]
        val manufactureGoodsMock: ManufactureGoods = mock[Webshop.ManufactureGoods]
        val validateOrderMock: ValidateOrder = mock[Webshop.ValidateOrder]

        val implementations = List(shipGoodsMock, sendInvoiceMock, manufactureGoodsMock, validateOrderMock).map(InteractionInstance.unsafeFrom(_))

        def createProcess(baker: Baker, recipeId: String): Future[Unit] = {
          for {
            _ <- baker.bake(recipeId, recipeInstanceId)
            // prepare mocks
            _ = when(shipGoodsMock.apply(anyString(), any[CustomerInfo]())).thenReturn(new ShipGoods.GoodsShipped(trackingId))
            _ = when(sendInvoiceMock.apply(any[CustomerInfo]())).thenReturn(new SendInvoice.InvoiceWasSent())
            _ = when(manufactureGoodsMock.apply(anyString())).thenReturn(new ManufactureGoods.GoodsManufactured(goods))
            _ = when(validateOrderMock.apply(anyString(), anyString())).thenReturn(new ValidateOrder.Valid())

            // process the events
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new CustomerInfoReceived(customerInfo)))
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new OrderPlaced(order)))
            _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, EventInstance.unsafeFrom(new PaymentMade()))
          } yield ()
        }

        (for {
          (baker, recipeId) <- setupAkkaBakerWithRecipe(recipe, implementations)(actorSystem)
          _ <- if (createNewCase) createProcess(baker, recipeId) else Future.unit

          expectedIngredients = ingredientMap(
            "customerInfo" -> customerInfo,
            "order" -> order,
            "goods" -> goods,
            "trackingId" -> trackingId)

          expectedEvents = eventList(
            new CustomerInfoReceived(customerInfo),
            new OrderPlaced(order),
            new ValidateOrder.Valid(),
            new PaymentMade(),
            new ManufactureGoods.GoodsManufactured(goods),
            new ShipGoods.GoodsShipped(trackingId),
            new SendInvoice.InvoiceWasSent()
          )

          state <- baker.getRecipeInstanceState(recipeInstanceId)
          _ = state.ingredients shouldBe expectedIngredients
          _ = state.eventNames shouldBe expectedEvents.map(_.name)
        } yield succeed).transform(
          { e => TestKit.shutdownActorSystem(actorSystem); e },
          { a => TestKit.shutdownActorSystem(actorSystem); a }
        )
      }
    }
    "be able to return" when {
      "an index of all processes in cluster mode" in {
        val journalId = java.util.UUID.randomUUID().toString
        val indexTestSystem = ActorSystem("indexTest", clusterLevelDBConfig(
          actorSystemName = "indexTest",
          port = 3005,
          journalPath = s"target/journal-$journalId",
          snapshotsPath = s"target/snapshots-$journalId"))
        val nrOfProcesses = 200

        for {
          (baker, recipeId) <- setupAkkaBakerWithRecipe("IndexTestCluster")(indexTestSystem)
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
        baker1 <- setupAkkaBakerWithNoRecipe(mockImplementations)(system1)
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
          baker2 <- setupAkkaBakerWithNoRecipe(mockImplementations)(system2)
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

  }
}
