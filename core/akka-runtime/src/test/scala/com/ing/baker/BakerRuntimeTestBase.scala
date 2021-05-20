package com.ing.baker

import akka.actor.ActorSystem
import akka.testkit.TestKit
import cats.effect.IO
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.CaseClassIngredient
import com.ing.baker.recipe.TestRecipe.{fireTwoEventsInteraction, _}
import com.ing.baker.recipe.common.Recipe
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.types.{Converters, Value}
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar
import java.nio.file.Paths
import java.util.UUID

import io.prometheus.client.CollectorRegistry

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._
import scala.language.postfixOps

trait BakerRuntimeTestBase
  extends AsyncWordSpecLike
    with Matchers
    with MockitoSugar
    with BeforeAndAfter
    with BeforeAndAfterAll {

  def actorSystemName: String

  implicit val timeout: FiniteDuration = 10 seconds
  implicit val contextShift = IO.contextShift(ExecutionContext.global)
  //Values to use for setting and checking the ingredients

  //Default values to be used for the ingredients in the tests
  protected val initialIngredientValue = "initialIngredient"
  protected val sievedIngredientValue = "sievedIngredient"
  protected val interactionOneOriginalIngredientValue = "interactionOneOriginalIngredient"
  protected val interactionOneIngredientValue = "interactionOneIngredient"
  protected val interactionTwoIngredientValue = "interactionTwoIngredient"
  protected val interactionTwoEventValue = EventFromInteractionTwo(interactionTwoIngredientValue)
  protected val interactionThreeIngredientValue = "interactionThreeIngredient"
  protected val interactionFourIngredientValue = "interactionFourIngredient"
  protected val interactionFiveIngredientValue = "interactionFiveIngredient"
  protected val interactionSixIngredientValue = "interactionSixIngredient"
  protected val caseClassIngredientValue = CaseClassIngredient(5, "this is a case class test")
  protected val errorMessage = "This is the error message"

  def ingredientMap(entries: (String, Any)*): Map[String, Value] =
    entries.map { case (name, obj) => name -> Converters.toValue(obj) }.toMap

  def eventList(events: Any*): Seq[EventInstance] = events.map(EventInstance.unsafeFrom)

  //Can be used to check the state after firing the initialEvent
  protected val afterInitialState = ingredientMap(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue
  )

  //Can be used to check the state after firing the initialEvent and SecondEvent
  protected val finalState = ingredientMap(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue,
    "interactionFourIngredient" -> interactionFourIngredientValue
  )

  protected val testInteractionOneMock: InteractionOne = mock[InteractionOne]
  protected val testInteractionTwoMock: InteractionTwo = mock[InteractionTwo]
  protected val testInteractionThreeMock: InteractionThree = mock[InteractionThree]
  protected val testInteractionFourMock: InteractionFour = mock[InteractionFour]
  protected val testInteractionFiveMock: InteractionFive = mock[InteractionFive]
  protected val testInteractionSixMock: InteractionSix = mock[InteractionSix]
  protected val testFireTwoEventsInteractionMock: fireTwoEventsInteraction = mock[fireTwoEventsInteraction]
  protected val testComplexIngredientInteractionMock: ComplexIngredientInteraction = mock[ComplexIngredientInteraction]
  protected val testCaseClassIngredientInteractionMock: CaseClassIngredientInteraction = mock[CaseClassIngredientInteraction]
  protected val testCaseClassIngredientInteraction2Mock: CaseClassIngredientInteraction2 = mock[CaseClassIngredientInteraction2]
  protected val testNonMatchingReturnTypeInteractionMock: NonMatchingReturnTypeInteraction = mock[NonMatchingReturnTypeInteraction]
  protected val testSieveInteractionMock: SieveInteraction = mock[SieveInteraction]
  protected val testOptionalIngredientInteractionMock: OptionalIngredientInteraction = mock[OptionalIngredientInteraction]
  protected val testProvidesNothingInteractionMock: ProvidesNothingInteraction = mock[ProvidesNothingInteraction]

  protected val mockImplementations: List[InteractionInstance] =
    List(
      testInteractionOneMock,
      testInteractionTwoMock,
      testInteractionThreeMock,
      testInteractionFourMock,
      testInteractionFiveMock,
      testInteractionSixMock,
      testFireTwoEventsInteractionMock,
      testComplexIngredientInteractionMock,
      testCaseClassIngredientInteractionMock,
      testCaseClassIngredientInteraction2Mock,
      testNonMatchingReturnTypeInteractionMock,
      testSieveInteractionMock,
      testOptionalIngredientInteractionMock,
      testProvidesNothingInteractionMock).map(InteractionInstance.unsafeFrom(_))

  def writeRecipeToSVGFile(recipe: CompiledRecipe) = {
    import guru.nidi.graphviz.engine.{Format, Graphviz}
    import guru.nidi.graphviz.parse.Parser
    val g = (new Parser()).read(recipe.getRecipeVisualization)
    Graphviz.fromGraph(g).render(Format.SVG).toFile(Paths.get(recipe.name).toFile)
  }

  protected def localLevelDBConfig(actorSystemName: String,
                                   journalInitializeTimeout: FiniteDuration = 10 seconds,
                                   journalPath: String = "target/journal",
                                   snapshotsPath: String = "target/snapshots"): Config =
    ConfigFactory.parseString(
      s"""
         |include "baker.conf"
         |
         |akka {
         |
         |  actor {
         |    provider = "akka.actor.LocalActorRefProvider"
         |    allow-java-serialization = off
         |    serialize-messages = off
         |    serialize-creators = off
         |  }
         |
         |  persistence {
         |     journal.plugin = "akka.persistence.journal.leveldb"
         |     journal.leveldb.dir = "$journalPath"
         |
         |     snapshot-store.plugin = "akka.persistence.snapshot-store.local"
         |     snapshot-store.local.dir = "$snapshotsPath"
         |
         |     auto-start-snapshot-stores = [ "akka.persistence.snapshot-store.local"]
         |     auto-start-journals = [ "akka.persistence.journal.leveldb" ]
         |
         |     journal.leveldb.native = off
         |  }
         |
         |  loggers = ["akka.event.slf4j.Slf4jLogger"]
         |  loglevel = "DEBUG"
         |  logging-filter = "akka.event.slf4j.Slf4jLoggingFilter"
         |}
         |
         |baker {
         |  actor.provider = "local"
         |  actor.read-journal-plugin = "akka.persistence.query.journal.leveldb"
         |  journal-initialize-timeout = $journalInitializeTimeout
         |
         |  recipe-manager-type = "actor"
         |}
         |
         |logging.root.level = DEBUG
    """.stripMargin)

  protected def clusterLevelDBConfig(actorSystemName: String,
                                     port: Int,
                                     journalInitializeTimeout: FiniteDuration = 10 seconds,
                                     journalPath: String = "target/journal",
                                     snapshotsPath: String = "target/snapshots"): Config =

    ConfigFactory.parseString(
      s"""
         |akka {
         |
         |  actor.provider = "akka.cluster.ClusterActorRefProvider"
         |
         |  remote.artery {
         |    canonical.hostname = localhost
         |    canonical.port = $port
         |  }
         |}
         |
         |baker {
         |  actor.provider = "cluster-sharded"
         |  cluster.seed-nodes = ["akka://$actorSystemName@localhost:$port"]
         |}
    """.stripMargin).withFallback(localLevelDBConfig(actorSystemName, journalInitializeTimeout, journalPath, snapshotsPath))

  implicit protected val defaultActorSystem: ActorSystem = ActorSystem(actorSystemName)

  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(defaultActorSystem)
  }

  /**
    * Returns a Baker instance that contains a simple recipe that can be used in tests
    * It als sets mocks that return happy flow responses for the interactions
    *
    * This recipe contains: See TestRecipe.png for a visualization
    *
    * @param recipeName A unique name that is needed for the recipe to insure that the tests do not interfere with each other
    * @return
    */
  protected def setupBakerWithRecipe(recipeName: String, appendUUIDToTheRecipeName: Boolean = true)
                                    (implicit actorSystem: ActorSystem): Future[(Baker, String)] = {
    val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
    val recipe = getRecipe(newRecipeName)
    setupMockResponse()
    setupBakerWithRecipe(recipe, mockImplementations)(actorSystem)
  }

  protected def setupBakerWithRecipe(recipe: Recipe, implementations: List[InteractionInstance])
                                    (implicit actorSystem: ActorSystem): Future[(Baker, String)] = {
    implicit val contextShift = IO.contextShift(actorSystem.dispatcher)
    val baker = AkkaBaker(ConfigFactory.load(), actorSystem, LocalInteractions(implementations))
    baker.addRecipe(RecipeCompiler.compileRecipe(recipe)).map(baker -> _)(actorSystem.dispatcher)
  }

  protected def setupBakerWithNoRecipe()(implicit actorSystem: ActorSystem): Future[Baker] = {
    setupMockResponse()
    implicit val contextShift = IO.contextShift(actorSystem.dispatcher)
    Future.successful(AkkaBaker(ConfigFactory.load(), actorSystem, LocalInteractions(mockImplementations)))
  }

  protected def setupMockResponse(): Unit = {
    when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(Future.successful(InteractionOneSuccessful(interactionOneIngredientValue)))
    when(testInteractionTwoMock.apply(anyString())).thenReturn(interactionTwoEventValue)
    when(testInteractionThreeMock.apply(anyString(), anyString())).thenReturn(InteractionThreeSuccessful(interactionThreeIngredientValue))
    when(testInteractionFourMock.apply()).thenReturn(InteractionFourSuccessful(interactionFourIngredientValue))
    when(testInteractionFiveMock.apply(anyString(), anyString(), anyString())).thenReturn(InteractionFiveSuccessful(interactionFiveIngredientValue))
    when(testInteractionSixMock.apply(anyString())).thenReturn(InteractionSixSuccessful(interactionSixIngredientValue))
    when(testSieveInteractionMock.apply(anyString(), anyString())).thenReturn(SieveInteractionSuccessful(sievedIngredientValue))
  }

  protected def timeBlockInMilliseconds[T](block: => T): Long = {
    val t0 = System.nanoTime()
    block
    val t1 = System.nanoTime()
    val amountOfNanosecondsInOneMillisecond = 1000000
    val milliseconds = (t1 - t0) / amountOfNanosecondsInOneMillisecond

    milliseconds
  }

  protected def resetMocks(): Unit =
    reset(testInteractionOneMock,
      testInteractionTwoMock,
      testInteractionThreeMock,
      testInteractionFourMock,
      testInteractionFiveMock,
      testInteractionSixMock,
      testNonMatchingReturnTypeInteractionMock)

}
