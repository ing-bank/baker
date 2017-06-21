package com.ing.baker

import java.util.UUID

import akka.actor.ActorSystem
import akka.testkit.TestKit
import com.ing.baker.TestRecipeHelper._
import com.ing.baker.Webshop._
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient}
import com.ing.baker.recipe.scaladsl
import com.ing.baker.recipe.scaladsl.{Event, Ingredient, Ingredients, Interaction, Recipe, processId}
import com.ing.baker.runtime.core.{Baker, RuntimeEvent}
import com.typesafe.config.{Config, ConfigFactory}
import org.mockito.Matchers._
import org.mockito.Mockito._
import org.scalatest._
import org.scalatest.mock.MockitoSugar

import scala.concurrent.duration._
import scala.language.postfixOps


class NonSerializableObject()

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
  val sievedIngredient = Ingredient[String]("sievedIngredient")
  val nonSerializableIngredient = Ingredient[NonSerializableObject]("nonSerializableIngredient")

  //Events as used in the recipe & objects used in runtime
  val initialEvent = Event("InitialEvent", initialIngredient)
  case class InitialEvent(initialIngredient: String) {}

  val initialEventExtendedName = Event("InitialEventExtendedName", initialIngredientExtendedName)
  case class InitialEventExtendedName(initialIngredientExtendedName: String)
  val secondEvent = Event("SecondEvent")
  case class SecondEvent()
  val notUsedSensoryEvent = Event("NotUsedSensoryEvent")
  case class NotUsedSensoryEvent()
  val eventFromInteractionTwo = Event("EventFromInteractionTwo", interactionTwoIngredient)
  case class EventFromInteractionTwo(interactionTwoIngredient: String)
  val eventWithANonSerializableIngredient = Event("EventWithANonSerializableIngredient", nonSerializableIngredient)
  case class EventWithANonSerializableIngredient(nonSerializableObject: NonSerializableObject)

  //Interactions used in the recipe & implementations (we use traits instead of case classes since we use mocks for the real implementations
  val interactionOne = Interaction("InteractionOne", Ingredients(processId, initialIngredient), ProvidesIngredient(interactionOneOriginalIngredient))
  trait InteractionOne {
    def apply(processId: String, initialIngredient: String): String
  }

  val interactionTwo = Interaction("InteractionTwo", Ingredients(initialIngredientOld), FiresOneOfEvents(eventFromInteractionTwo))
  trait InteractionTwoImpl {
    val name: String = "InteractionTwo"
    def apply(initialIngredientOld: String): EventFromInteractionTwo
  }

  val interactionThree = Interaction("InteractionThree", Ingredients(interactionOneIngredient, interactionTwoIngredient), ProvidesIngredient(interactionThreeIngredient))
  trait InteractionThreeImpl {
    val name: String = "InteractionThree"
    def apply(interactionOneIngredient: String, interactionTwoIngredient: String): String
  }

  val interactionFour = Interaction("InteractionFour", Ingredients(), ProvidesIngredient(interactionFourIngredient))
  trait InteractionFourImpl {
    val name: String = "InteractionFour"
    def apply(): String
  }

  val interactionFive = Interaction("InteractionFive", Ingredients(processId, initialIngredient, initialIngredientExtendedName), ProvidesIngredient(interactionFiveIngredient))
  trait InteractionFiveImpl {
    val name: String = "InteractionFive"
    def apply(processId: String, initialIngredient: String, initialIngredientExtendedName: String): String
  }

  val interactionSix = Interaction("InteractionSix", Ingredients(initialIngredientExtendedName), ProvidesIngredient(interactionSixIngredient))
  trait InteractionSixImpl {
    val name: String = "InteractionSix"
    def apply(initialIngredientExtendedName: String): String
  }

  val sieveInteraction = Interaction("SieveInteraction", Ingredients(processId, initialIngredient), ProvidesIngredient(sievedIngredient))
  trait SieveInteractionImpl {
    val name: String = "SieveInteraction"
    def apply(processId: String, initialIngredient: String): String
  }

  val sieveInteractionWithoutDefaultConstructor = Interaction("SieveInteractionWithoutDefaultConstructor", Ingredients(processId, initialIngredient), ProvidesIngredient(sievedIngredient))
  trait SieveInteractionWithoutDefaultConstructorImpl {
    val name: String = "SieveInteractionWithoutDefaultConstructor"
    def apply(processId: String, initialIngredient: String): String
  }

  val NonSerializableEventInteraction = Interaction("NonSerializableEventInteraction", Ingredients(initialIngredient), FiresOneOfEvents(eventWithANonSerializableIngredient))
  trait NonSerializableEventInteractionImpl {
    val name: String = "NonSerializableEventInteraction"
    def apply(initialIngredient: String): EventWithANonSerializableIngredient
  }

  val NonSerializableIngredientInteraction = Interaction("NonSerializableIngredientInteraction", Ingredients(initialIngredient), ProvidesIngredient(nonSerializableIngredient))
  trait NonSerializableIngredientInteractionImpl {
    val name: String = "NonSerializableIngredientInteraction"
    def apply(initialIngredient: String): NonSerializableObject
  }

  val NonMatchingReturnTypeInteraction = Interaction("NonMatchingReturnTypeInteraction", Ingredients(initialIngredient), FiresOneOfEvents(eventFromInteractionTwo))
  trait NonMatchingReturnTypeInteractionImpl {
    val name: String = "NonMatchingReturnTypeInteraction"
    def apply(initialIngredient: String): EventFromInteractionTwo
  }
}

object Webshop {
  //Webshop ingredients, events, interactions
  case class CustomerObj(name: String, address: String, email: String)

  val order = Ingredient[String]("order")
  val name = Ingredient[String]("name")
  val address = Ingredient[String]("address")
  val email = Ingredient[String]("email")
  val customerInfo = Ingredient[CustomerObj]("customerInfo")
  val goods = Ingredient[String]("goods")
  val trackingId = Ingredient[String]("trackingId")
  val invoiceWasSent = Ingredient[Boolean]("invoiceWasSent")

  val OrderPlaced = Event("OrderPlaced", order)
  val Customer = Event("Customer", name, address, email)
  val CustomerInfoReceived = Event("CustomerInfoReceived", customerInfo)
  val PaymentMade = Event("PaymentMade")
  val Valid = Event("Valid")
  val Sorry = Event("Sorry")
  val GoodsManufactured = Event("GoodsManufactured", goods)
  val GoodsShipped = Event("GoodsShipped", trackingId)

  //an interaction can fire one of multiple events
  val ValidateOrder = Interaction(
    "ValidateOrder",
    order,
    FiresOneOfEvents(Valid, Sorry))

  //an interaction can fire a single event only
  val ManufactureGoods = Interaction(
    "ManufactureGoods",
    order,
    FiresOneOfEvents(GoodsManufactured))

  val ShipGoods = Interaction(
    "ShipGoods",
    Ingredients(goods, customerInfo),
    FiresOneOfEvents(GoodsShipped))

  //instead of an event, an interaction can directly provide a new ingredient
  //any primitive type or a case class is supported
  val SendInvoice = Interaction(
    "SendInvoice",
    customerInfo,
    ProvidesIngredient(invoiceWasSent))
}



trait TestRecipeHelper
  extends WordSpecLike
    with Matchers
    with MockitoSugar
    with BeforeAndAfter
    with BeforeAndAfterAll {
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
  protected val errorMessage = "This is the error message"

  //Can be used to check the state after firing the initialEvent
  protected val afterInitialState = Map(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue
  )

  //Can be used to check the state after firing the initialEvent and SecondEvent
  protected val finalState = Map(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue,
    "interactionFourIngredient" -> interactionFourIngredientValue
  )

  protected val testInteractionOneMock: InteractionOne = mock[InteractionOne]
  protected val testInteractionTwoMock: InteractionTwoImpl = mock[InteractionTwoImpl]
  protected val testInteractionThreeMock: InteractionThreeImpl = mock[InteractionThreeImpl]
  protected val testInteractionFourMock: InteractionFourImpl = mock[InteractionFourImpl]
  protected val testInteractionFiveMock: InteractionFiveImpl = mock[InteractionFiveImpl]
  protected val testInteractionSixMock: InteractionSixImpl = mock[InteractionSixImpl]
  protected val testNonSerializableEventInteractionMock: NonSerializableEventInteractionImpl =
    mock[NonSerializableEventInteractionImpl]
  protected val testNonSerializableIngredientInteractionMock: NonSerializableIngredientInteractionImpl =
    mock[NonSerializableIngredientInteractionImpl]
  protected val testNonMatchingReturnTypeInteractionMock: NonMatchingReturnTypeInteractionImpl =
    mock[NonMatchingReturnTypeInteractionImpl]
  protected val testSieveInteractionMock: SieveInteractionImpl = mock[SieveInteractionImpl]

    protected val mockImplementations: Map[String, () => AnyRef] =
    Map(
      "InteractionOne" -> (() => testInteractionOneMock),
      "InteractionTwo" -> (() => testInteractionTwoMock),
      "InteractionThree" -> (() => testInteractionThreeMock),
      "InteractionFour" -> (() => testInteractionFourMock),
      "InteractionFive" -> (() => testInteractionFiveMock),
      "InteractionSix" -> (() => testInteractionSixMock),
      "NonSerializableIngredientInteraction" -> (() => testNonSerializableIngredientInteractionMock),
      "NonSerializableEventInteraction" -> (() => testNonSerializableEventInteractionMock),
      "NonMatchingReturnTypeInteraction" -> (() => testNonMatchingReturnTypeInteractionMock),
      "SieveInteraction" -> (() => testSieveInteractionMock))

  protected def levelDbConfig(actorSystemName: String, port: Int): Config = ConfigFactory.parseString(
    s"""
       |akka {
       |  actor.provider = "akka.cluster.ClusterActorRefProvider"
       |
       |  actor {
       |    provider = "akka.cluster.ClusterActorRefProvider"
       |    allow-java-serialization = off
       |  }
       |
       |  remote {
       |    netty.tcp {
       |      hostname = localhost
       |      port = $port
       |    }
       |  }
       |
       |  cluster.seed-nodes = ["akka.tcp://$actorSystemName@localhost:$port"]
       |
       |  persistence {
       |     journal.plugin = "akka.persistence.journal.leveldb"
       |     journal.leveldb.dir = "target/journal"
       |
       |     snapshot-store.plugin = "akka.persistence.snapshot-store.local"
       |     snapshot-store.local.dir = "target/snapshots"
       |
       |     auto-start-snapshot-stores = [ "akka.persistence.snapshot-store.local"]
       |     auto-start-journals = [ "akka.persistence.journal.leveldb" ]
       |
       |     journal.leveldb.native = off
       |  }
       |}
       |
       |baker {
       |  actor.provider = "cluster-sharded"
       |  actor.read-journal-plugin = "akka.persistence.query.journal.leveldb"
       |}
       |
       |logging.root.level = DEBUG
    """.stripMargin)

  implicit protected val defaultActorSystem = ActorSystem("BakerSpec")

  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(defaultActorSystem)
  }

  protected def getComplexRecipe(recipeName: String): Recipe =
    Recipe(recipeName)
      .withInteractions(
        interactionOne
          .withOverriddenOutputIngredientName("interactionOneIngredient")
          .withIncrementalBackoffOnFailure(initialDelay = 10 millisecond, maximumRetries = 3),
        interactionTwo
          .withOverriddenIngredientName("initialIngredientOld", "initialIngredient"),
        interactionThree
          .withMaximumInteractionCount(1),
        interactionFour
          .withRequiredEvents(secondEvent, eventFromInteractionTwo),
        interactionFive,
        interactionSix,
        sieveInteraction
      )
      .withSensoryEvents(
        initialEvent,
        initialEventExtendedName,
        secondEvent,
        notUsedSensoryEvent)

  protected val getWebshopRecipe: Recipe =
    Recipe("Webshop")
        .withInteractions(
        ValidateOrder,
        ManufactureGoods
          .withRequiredEvents(Valid, PaymentMade),
        ShipGoods,
        SendInvoice
          .withRequiredEvent(GoodsShipped)
      )
      .withSensoryEvents(
        CustomerInfoReceived,
        OrderPlaced,
        PaymentMade)

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
                                    (implicit actorSystem: ActorSystem): Baker = {
    val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
    val recipe = getComplexRecipe(newRecipeName)
    setupMockResponse()

    new Baker(
      compiledRecipe = RecipeCompiler.compileRecipe(recipe),
      implementations = mockImplementations)(actorSystem)
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
      testNonMatchingReturnTypeInteractionMock,
      testNonSerializableEventInteractionMock,
      testNonSerializableIngredientInteractionMock)
}
