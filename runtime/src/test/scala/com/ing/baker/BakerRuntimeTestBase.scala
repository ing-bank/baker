package com.ing.baker

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.TestRecipe._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common
import com.ing.baker.runtime.core.Baker
import com.ing.baker.types.{Converters, Value}
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.scalatest._
import org.scalatest.mockito.MockitoSugar

import scala.concurrent.duration._
import scala.language.postfixOps

trait BakerRuntimeTestBase
  extends WordSpecLike
    with Matchers
    with MockitoSugar
    with BeforeAndAfter
    with BeforeAndAfterAll {

  def actorSystemName: String

  implicit val timeout: FiniteDuration = 10 seconds

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
  protected val testComplexIngredientInteractionMock: ComplexIngredientInteraction = mock[ComplexIngredientInteraction]
  protected val testCaseClassIngredientInteractionMock: CaseClassIngredientInteraction = mock[CaseClassIngredientInteraction]
  protected val testCaseClassIngredientInteraction2Mock: CaseClassIngredientInteraction2 = mock[CaseClassIngredientInteraction2]
  protected val testNonMatchingReturnTypeInteractionMock: NonMatchingReturnTypeInteraction = mock[NonMatchingReturnTypeInteraction]
  protected val testSieveInteractionMock: SieveInteraction = mock[SieveInteraction]
  protected val testOptionalIngredientInteractionMock: OptionalIngredientInteraction = mock[OptionalIngredientInteraction]
  protected val testProvidesNothingInteractionMock: ProvidesNothingInteraction = mock[ProvidesNothingInteraction]

  protected val mockImplementations: Seq[AnyRef] =
    Seq(
      testInteractionOneMock,
      testInteractionTwoMock,
      testInteractionThreeMock,
      testInteractionFourMock,
      testInteractionFiveMock,
      testInteractionSixMock,
      testComplexIngredientInteractionMock,
      testCaseClassIngredientInteractionMock,
      testCaseClassIngredientInteraction2Mock,
      testNonMatchingReturnTypeInteractionMock,
      testSieveInteractionMock,
      testOptionalIngredientInteractionMock,
      testProvidesNothingInteractionMock)

  protected def levelDbConfig(actorSystemName: String,
                              port: Int,
                              journalInitializeTimeout: FiniteDuration = 10 seconds,
                              journalPath: String = "target/journal",
                              snapshotsPath: String = "target/snapshots"): Config =

    ConfigFactory.parseString(
    s"""
       |include "baker.conf"
       |
       |akka {
       |  actor.provider = "akka.cluster.ClusterActorRefProvider"
       |
       |  actor {
       |    provider = "akka.cluster.ClusterActorRefProvider"
       |    allow-java-serialization = off
       |    serialize-messages = on
       |    serialize-creators = off
       |  }
       |
       |  remote {
       |    netty.tcp {
       |      hostname = localhost
       |      port = $port
       |    }
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
       |  actor.provider = "cluster-sharded"
       |  actor.read-journal-plugin = "akka.persistence.query.journal.leveldb"
       |  journal-initialize-timeout = $journalInitializeTimeout
       |  cluster.seed-nodes = ["akka.tcp://$actorSystemName@localhost:$port"]
       |}
       |
       |logging.root.level = DEBUG
    """.stripMargin)

  implicit protected val defaultActorSystem = ActorSystem(actorSystemName)

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
                                    (implicit actorSystem: ActorSystem): (Baker, String) = {
    val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
    val recipe = getRecipe(newRecipeName)
    setupMockResponse()

    setupBakerWithRecipe(recipe, mockImplementations)(actorSystem)
  }

  protected def setupBakerWithRecipe(recipe: common.Recipe, implementations: Seq[AnyRef])
                                    (implicit actorSystem: ActorSystem): (Baker, String) = {

    val baker = new Baker()(actorSystem)
    baker.addImplementation(implementations)
    val recipeId = baker.addRecipe(RecipeCompiler.compileRecipe(recipe))
    (baker, recipeId)
  }

  protected def setupBakerWithNoRecipe()(implicit actorSystem: ActorSystem): Baker = {
    setupMockResponse()
    val baker = new Baker()(actorSystem)
    baker.addImplementation(mockImplementations)
    baker
  }

  protected def setupMockResponse(): Unit = {
    when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(interactionOneIngredientValue)
    when(testInteractionTwoMock.apply(anyString())).thenReturn(interactionTwoEventValue)
    when(testInteractionThreeMock.apply(anyString(), anyString())).thenReturn(interactionThreeIngredientValue)
    when(testInteractionFourMock.apply()).thenReturn(interactionFourIngredientValue)
    when(testInteractionFiveMock.apply(anyString(), anyString(), anyString())).thenReturn(interactionFiveIngredientValue)
    when(testInteractionSixMock.apply(anyString())).thenReturn(interactionSixIngredientValue)
    when(testSieveInteractionMock.apply(anyString(), anyString())).thenReturn(sievedIngredientValue)
  }

  protected def timeBlockInMilliseconds[T](block: => T): Long = {
    val t0 = System.nanoTime()
    block
    val t1 = System.nanoTime()
    val amountOfNanosecondsInOneMillisecond = 1000000
    val milliseconds = (t1 - t0) / amountOfNanosecondsInOneMillisecond

    milliseconds
  }

  protected def resetMocks =
    reset(testInteractionOneMock,
      testInteractionTwoMock,
      testInteractionThreeMock,
      testInteractionFourMock,
      testInteractionFiveMock,
      testInteractionSixMock,
      testNonMatchingReturnTypeInteractionMock)
}
