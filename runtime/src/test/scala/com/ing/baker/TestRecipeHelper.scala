package com.ing.baker

import java.util.{Optional, UUID}

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.TestRecipeHelper._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionFailureStrategy, ProvidesIngredient}
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.core.Baker
import com.ing.baker.types.{Converters, Value}
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.scalatest._
import org.scalatest.mockito.MockitoSugar

import scala.concurrent.duration._
import scala.language.postfixOps

//By adding the javadsl Ingredient tag the object will be serialized by Kryo
class ComplexObjectIngredient(value: String)

case class CaseClassIngredient(a: Int, b: String)

object TestRecipeHelper {
  //Ingredients as used in the recipe
  val initialIngredientOld = Ingredient[String]("initialIngredientOld")
  val initialIngredient = Ingredient[String]("initialIngredient")
  val interactionOneOriginalIngredient = Ingredient[String]("interactionOneOriginalIngredient")
  val initialIngredientExtendedName = Ingredient[String]("initialIngredientExtendedName")
  val interactionOneIngredient = Ingredient[String]("interactionOneIngredient")
  val interactionTwoIngredient = Ingredient[String]("interactionTwoIngredient")
  val interactionThreeIngredient = Ingredient[String]("interactionThreeIngredient")
  val interactionFourIngredient = Ingredient[String]("interactionFourIngredient")
  val interactionFiveIngredient = Ingredient[String]("interactionFiveIngredient")
  val interactionSixIngredient = Ingredient[String]("interactionSixIngredient")
  val interactionSevenIngredient1 = Ingredient[String]("interactionSevenIngredient1")
  val interactionSevenIngredient2 = Ingredient[String]("interactionSevenIngredient2")
  val sievedIngredient = Ingredient[String]("sievedIngredient")
  val complexObjectIngredient = Ingredient[ComplexObjectIngredient]("complexOjectIngredient")
  val caseClassIngredient = Ingredient[CaseClassIngredient]("caseClassIngredient")
  val missingJavaOptional: Ingredient[Optional[String]] = Ingredient[Optional[String]]("missingJavaOptional")
  val missingJavaOptionalDirectString: Ingredient[String] = Ingredient[String]("missingJavaOptional")
  val missingJavaOptional2: Ingredient[Optional[Int]] = Ingredient[Optional[Int]]("missingJavaOptional2")
  val missingScalaOptional: Ingredient[Option[String]] = Ingredient[Option[String]]("missingScalaOptional")
  val missingScalaOptionalDirectString: Ingredient[String] = Ingredient[String]("missingScalaOptional")
  val missingScalaOptional2: Ingredient[Option[Int]] = Ingredient[Option[Int]]("missingScalaOptional2")

  //Events as used in the recipe & objects used in runtime
  val initialEvent = Event("InitialEvent", initialIngredient, None)

  case class InitialEvent(initialIngredient: String)

  val initialEventExtendedName = Event("InitialEventExtendedName", initialIngredientExtendedName)

  case class InitialEventExtendedName(initialIngredientExtendedName: String)

  val secondEvent = Event("SecondEvent")

  case class SecondEvent()

  val thirdEvent = Event("ThirdEvent")

  case class ThirdEvent()

  val fourthEvent = Event("FourthEvent")

  case class FourthEvent()

  val notUsedSensoryEvent = Event("NotUsedSensoryEvent")

  case class NotUsedSensoryEvent()

  val eventFromInteractionTwo = Event("EventFromInteractionTwo", interactionTwoIngredient)

  case class EventFromInteractionTwo(interactionTwoIngredient: String)

  val event1FromInteractionSeven = Event("Event1FromInteractionSeven", interactionSevenIngredient1)

  case class Event1FromInteractionSeven(interactionSevenIngredient1: String)

  val event2FromInteractionSeven = Event("Event2FromInteractionSeven", interactionSevenIngredient2)

  case class Event2FromInteractionSeven(interactionSevenIngredient2: String)

  val emptyEvent = Event("EmptyEvent")

  case class EmptyEvent()

  val exhaustedEvent = Event("RetryExhausted")

  val unboxedProviderEvent = Event("UnboxedProviderEvent", missingJavaOptionalDirectString, initialIngredient, missingScalaOptionalDirectString)

  case class UnboxedProviderEvent(missingJavaOptional: String, initialIngredient: String, missingScalaOptional: String)

  //Interactions used in the recipe & implementations (we use traits instead of case classes since we use mocks for the real implementations
  val interactionOne =
    Interaction("InteractionOne",
      Ingredients(processId, initialIngredient),
      ProvidesIngredient(interactionOneOriginalIngredient))

  trait InteractionOne {
    def name: String = "InteractionOne"

    def apply(processId: String, initialIngredient: String): String
  }

  val interactionTwo =
    Interaction("InteractionTwo",
      Ingredients(initialIngredientOld),
      FiresOneOfEvents(eventFromInteractionTwo))

  trait InteractionTwo {
    val name: String = "InteractionTwo"

    def apply(initialIngredientOld: String): EventFromInteractionTwo
  }

  val interactionThree =
    Interaction("InteractionThree",
      Ingredients(interactionOneIngredient, interactionTwoIngredient),
      ProvidesIngredient(interactionThreeIngredient))

  trait InteractionThree {
    val name: String = "InteractionThree"

    def apply(interactionOneIngredient: String, interactionTwoIngredient: String): String
  }

  val interactionFour =
    Interaction("InteractionFour",
      Ingredients(),
      ProvidesIngredient(interactionFourIngredient))

  trait InteractionFour {
    val name: String = "InteractionFour"

    def apply(): String
  }

  val interactionFive =
    Interaction("InteractionFive",
      Ingredients(processId, initialIngredient, initialIngredientExtendedName),
      ProvidesIngredient(interactionFiveIngredient))

  trait InteractionFive {
    val name: String = "InteractionFive"

    def apply(processId: String, initialIngredient: String, initialIngredientExtendedName: String): String
  }

  val interactionSix =
    Interaction("InteractionSix",
      Ingredients(initialIngredientExtendedName),
      ProvidesIngredient(interactionSixIngredient))

  trait InteractionSix {
    val name: String = "InteractionSix"

    def apply(initialIngredientExtendedName: String): String
  }

  val interactionSeven =
    Interaction("InteractionSeven",
      Ingredients(initialIngredient),
      FiresOneOfEvents(event1FromInteractionSeven, event2FromInteractionSeven))

  trait InteractionSeven {
    val name: String = "InteractionSeven"

    def apply(initialIngredient: String): String
  }

  val interactionEight =
    Interaction("InteractionEight",
      Ingredients(interactionSevenIngredient1, interactionSevenIngredient2),
      common.ProvidesNothing)

  trait InteractionEight {
    val name: String = "InteractionEight"

    def apply(interactionSevenIngredient1: String, interactionSevenIngredient2: String): Unit
  }

  val providesNothingInteraction =
    Interaction("ProvidesNothingInteraction",
      Ingredients(initialIngredient),
      common.ProvidesNothing)

  trait ProvidesNothingInteraction {
    val name: String = "ProvidesNothingInteraction"

    def apply(initialIngredient: String): Unit
  }

  val sieveInteraction =
    Interaction("SieveInteraction",
      Ingredients(processId, initialIngredient),
      ProvidesIngredient(sievedIngredient))

  trait SieveInteraction {
    val name: String = "SieveInteraction"

    def apply(processId: String, initialIngredient: String): String
  }

  val sieveInteractionWithoutDefaultConstructor =
    Interaction("SieveInteractionWithoutDefaultConstructor",
      Ingredients(processId, initialIngredient),
      ProvidesIngredient(sievedIngredient))

  trait SieveInteractionWithoutDefaultConstructor {
    val name: String = "SieveInteractionWithoutDefaultConstructor"

    def apply(processId: String, initialIngredient: String): String
  }

  val complexIngredientInteraction =
    Interaction("ComplexIngredientInteraction",
      Ingredients(initialIngredient),
      ProvidesIngredient(complexObjectIngredient))

  trait ComplexIngredientInteraction {
    val name: String = "ComplexIngredientInteraction"

    def apply(initialIngredient: String): ComplexObjectIngredient
  }

  val caseClassIngredientInteraction =
    Interaction("CaseClassIngredientInteraction",
      Ingredients(initialIngredient),
      ProvidesIngredient(caseClassIngredient))

  trait CaseClassIngredientInteraction {
    val name: String = "CaseClassIngredientInteraction"

    def apply(initialIngredient: String): CaseClassIngredient
  }

  val caseClassIngredientInteraction2 =
    Interaction("CaseClassIngredientInteraction2",
      Ingredients(caseClassIngredient),
      FiresOneOfEvents(emptyEvent))

  trait CaseClassIngredientInteraction2 {
    val name: String = "CaseClassIngredientInteraction2"

    def apply(caseClassIngredient: CaseClassIngredient): EmptyEvent
  }

  val NonMatchingReturnTypeInteraction =
    Interaction("NonMatchingReturnTypeInteraction",
      Ingredients(initialIngredient),
      FiresOneOfEvents(eventFromInteractionTwo))

  trait NonMatchingReturnTypeInteraction {
    val name: String = "NonMatchingReturnTypeInteraction"

    def apply(initialIngredient: String): EventFromInteractionTwo
  }

  val optionalIngredientInteraction =
    Interaction("OptionalIngredientInteraction",
      Seq(
        missingJavaOptional,
        missingJavaOptional2,
        missingScalaOptional,
        missingScalaOptional2,
        initialIngredient),
      common.ProvidesNothing)

  trait OptionalIngredientInteraction {
    val name: String = "OptionalIngredientInteraction"

    def apply(missingJavaOptional: Optional[String],
              missingJavaOptional2: Optional[Integer],
              missingScalaOptional: Option[String],
              missingScalaOptional2: Option[Integer],
              initialIngredient: String)
  }

}

trait TestRecipeHelper
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

  protected def levelDbConfig(actorSystemName: String, port: Int, journalInitializeTimeout: FiniteDuration = 10 seconds, journalPath: String = "target/journal", snapshotsPath: String = "target/snapshots"): Config = ConfigFactory.parseString(
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

  protected def getComplexRecipe(recipeName: String): Recipe =
    Recipe(recipeName)
      .withInteractions(
        interactionOne
          .withOverriddenOutputIngredientName("interactionOneIngredient")
          .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff(initialDelay = 10 millisecond, maximumRetries = 3)),
        interactionTwo
          .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"),
        interactionThree
          .withMaximumInteractionCount(1),
        interactionFour
          .withRequiredEvents(secondEvent, eventFromInteractionTwo),
        interactionFive,
        interactionSix,
        providesNothingInteraction,
        sieveInteraction
      )
      .withSensoryEvents(
        initialEvent,
        initialEventExtendedName,
        secondEvent,
        notUsedSensoryEvent)

  /**
    * Returns a Baker instance that contains a simple recipe that can be used in tests
    * It als sets mocks that return happy flow responses for the interactions
    *
    * This recipe contains:
    * A split from 1 ingredient to two interactions
    * A join after the two interactions that give out ingredients into a third interaction
    * To See a visualisation of the recipe go to http://www.webgraphviz.com/ and use the following:
    * *
    * digraph {
    * node [fontname = "ING Me", fontsize = 22, fontcolor = white]
    * pad = 0.2
    * interactionTwo -> EventFromInteractionTwo
    * interactionOneIngredient [shape = circle, color = "#FF6200", style = filled]
    * EventFromInteractionTwo -> interactionTwoIngredient
    * interactionTwoIngredient -> interactionThree
    * interactionTwo [shape = rect, margin = 0.5, color = "#525199", style = "rounded, filled", penwidth = 2]
    * interactionThree [shape = rect, margin = 0.5, color = "#525199", style = "rounded, filled", penwidth = 2]
    * interactionFour [shape = rect, margin = 0.5, color = "#525199", style = "rounded, filled", penwidth = 2]
    * interactionFourIngredient [shape = circle, color = "#FF6200", style = filled]
    * initialIngredient -> "multi:initialIngredient"
    * SecondEvent -> interactionFour
    * interactionThreeIngredient [shape = circle, color = "#FF6200", style = filled]
    * InitialEvent -> initialIngredient
    * interactionThree -> interactionThreeIngredient
    * interactionFour -> interactionFourIngredient
    * interactionOne [shape = rect, margin = 0.5, color = "#525199", style = "rounded, filled", penwidth = 2]
    * interactionOne -> interactionOneIngredient
    * InitialEvent [shape = diamond, margin = 0.3, style = "rounded, filled", color = "#767676"]
    * "multi:initialIngredient" -> interactionTwo
    * SecondEvent [shape = diamond, margin = 0.3, style = "rounded, filled", color = "#767676"]
    * interactionTwoIngredient [shape = circle, color = "#FF6200", style = filled]
    * "multi:initialIngredient" [shape = point, fillcolor = "#D0D93C", width = 0.3, height = 0.3]
    * EventFromInteractionTwo -> interactionFour
    * EventFromInteractionTwo [shape = diamond, margin = 0.3, style = "rounded, filled", color = "#767676"]
    * interactionOneIngredient -> interactionThree
    * initialIngredient [shape = circle, color = "#FF6200", style = filled]
    * "multi:initialIngredient" -> interactionOne
    * }
    *
    * @param recipeName A unique name that is needed for the recipe to insure that the tests do not interfere with each other
    * @return
    */
  protected def setupBakerWithRecipe(recipeName: String, appendUUIDToTheRecipeName: Boolean = true)
                                    (implicit actorSystem: ActorSystem): (Baker, String) = {
    val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
    val recipe = getComplexRecipe(newRecipeName)
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

    //    when(testInteractionOneMock.name).thenReturn("InteractionOne");
    //    when(testInteractionTwoMock.name).thenReturn("InteractionTwo");
    //    when(testInteractionThreeMock.name).thenReturn("InteractionThree")
    //    when(testInteractionFourMock.name).thenReturn("InteractionFour")
    //    when(testInteractionFiveMock.name).thenReturn("InteractionFive")
    //    when(testInteractionSixMock.name).thenReturn("InteractionSix")
    //    when(testComplexIngredientInteractionMock.name).thenReturn("ComplexIngredientInteraction")
    //    when(testCaseClassIngredientInteractionMock.name).thenReturn("CaseClassIngredientInteraction")
    //    when(testCaseClassIngredientInteraction2Mock.name).thenReturn("CaseClassIngredientInteraction2")
    //    when(testNonMatchingReturnTypeInteractionMock.name).thenReturn("NonMatchingReturnTypeInteraction")
    //    when(testSieveInteractionMock.name).thenReturn("SieveInteraction")
    //    when(testOptionalIngredientInteractionMock.name).thenReturn("OptionalIngredientInteraction")
    //    when(testProvidesNothingInteractionMock.name).thenReturn("providesNothingInteraction")
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
