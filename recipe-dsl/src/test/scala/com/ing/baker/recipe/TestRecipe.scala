package com.ing.baker.recipe

import java.util.Optional

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.scaladsl._

import scala.concurrent.duration._

//By adding the javadsl Ingredient tag the object will be serialized by Kryo
class ComplexObjectIngredient(value: String)

case class CaseClassIngredient(a: Int, b: String)

object TestRecipe {

  //inputIngredients = Seq as used in the recipe
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
  val initialEvent = Event("InitialEvent", Seq(initialIngredient), maxFiringLimit = None)

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

  case class InteractionOneSuccessful(interactionOneOriginalIngredient: String)

  val interactionOneSuccessful: common.Event = Event[InteractionOneSuccessful]

  //Interactions used in the recipe & implementations (we use traits instead of case classes since we use mocks for the real implementations
  val interactionOne =
    Interaction(
      name = "InteractionOne",
      inputIngredients = Seq(processId, initialIngredient),
      output = Seq(interactionOneSuccessful))

  trait InteractionOne {
    def name: String = "InteractionOne"

    def apply(processId: String, initialIngredient: String): InteractionOneSuccessful
  }

  val interactionTwo =
    Interaction(
      name = "InteractionTwo",
      inputIngredients = Seq(initialIngredientOld),
      output = Seq(eventFromInteractionTwo))

  trait InteractionTwo {
    val name: String = "InteractionTwo"

    def apply(initialIngredientOld: String): EventFromInteractionTwo
  }

  case class InteractionThreeSuccessful(interactionThreeIngredient: String)

  val interactionThree =
    Interaction(
      name = "InteractionThree",
      inputIngredients = Seq(interactionOneIngredient, interactionTwoIngredient),
      output = Seq(Event[InteractionThreeSuccessful]))

  trait InteractionThree {
    val name: String = "InteractionThree"

    def apply(interactionOneIngredient: String, interactionTwoIngredient: String): InteractionThreeSuccessful
  }

  case class InteractionFourSuccessful(interactionFourIngredient: String)

  val interactionFour =
    Interaction(
      name = "InteractionFour",
      inputIngredients = Seq.empty,
      output = Seq(Event[InteractionFourSuccessful]))

  trait InteractionFour {
    val name: String = "InteractionFour"

    def apply(): InteractionFourSuccessful
  }

  case class InteractionFiveSuccessful(interactionFiveIngredient: String)

  val interactionFive =
    Interaction(
      name = "InteractionFive",
      inputIngredients = Seq(processId, initialIngredient, initialIngredientExtendedName),
      output = Seq(Event[InteractionFiveSuccessful]))

  trait InteractionFive {
    val name: String = "InteractionFive"

    def apply(processId: String, initialIngredient: String, initialIngredientExtendedName: String): InteractionFiveSuccessful
  }

  case class InteractionSixSuccessful(interactionSixIngredient: String)

  val interactionSix =
    Interaction(
      name = "InteractionSix",
      inputIngredients = Seq(initialIngredientExtendedName),
      output = Seq(Event[InteractionSixSuccessful]))

  trait InteractionSix {
    val name: String = "InteractionSix"

    def apply(initialIngredientExtendedName: String): InteractionSixSuccessful
  }

  val interactionSeven =
    Interaction(
      name = "InteractionSeven",
      inputIngredients = Seq(initialIngredient),
      output = Seq(event1FromInteractionSeven, event2FromInteractionSeven))

  trait InteractionSeven {
    val name: String = "InteractionSeven"

    def apply(initialIngredient: String): String
  }

  val interactionEight =
    Interaction(
      name = "InteractionEight",
      inputIngredients = Seq(interactionSevenIngredient1, interactionSevenIngredient2),
      output = Seq.empty)

  trait InteractionEight {
    val name: String = "InteractionEight"

    def apply(interactionSevenIngredient1: String, interactionSevenIngredient2: String): Unit
  }

  val fireTwoEventsInteraction =
    Interaction(
      name = "fireTwoEventsInteraction",
      inputIngredients = Seq(initialIngredient),
      output = Seq(eventFromInteractionTwo, event1FromInteractionSeven))

  trait fireTwoEventsInteraction {
    val name: String = "fireTwoEventsInteraction"

    def apply(initialIngredient: String): Event1FromInteractionSeven
  }

  val providesNothingInteraction =
    Interaction(
      name = "ProvidesNothingInteraction",
      inputIngredients = Seq(initialIngredient),
      output = Seq.empty)

  trait ProvidesNothingInteraction {
    val name: String = "ProvidesNothingInteraction"

    def apply(initialIngredient: String): Unit
  }

  case class SieveInteractionSuccessful(sievedIngredient: String)

  val sieveInteraction =
    Interaction(
      name = "SieveInteraction",
      inputIngredients = Seq(processId, initialIngredient),
      output = Seq(Event[SieveInteractionSuccessful]))

  trait SieveInteraction {
    val name: String = "SieveInteraction"

    def apply(processId: String, initialIngredient: String): SieveInteractionSuccessful
  }

  case class ComplexIngredientInteractionSuccessful(complexOjectIngredient: ComplexObjectIngredient)

  val complexIngredientInteraction =
    Interaction(
      name = "ComplexIngredientInteraction",
      inputIngredients = Seq(initialIngredient),
      Seq(Event[ComplexIngredientInteractionSuccessful]))

  trait ComplexIngredientInteraction {
    val name: String = "ComplexIngredientInteraction"

    def apply(initialIngredient: String): ComplexIngredientInteractionSuccessful
  }

  case class CaseClassIngredientInteractionSuccessful(caseClassIngredient: CaseClassIngredient)

  val caseClassIngredientInteraction =
    Interaction(
      name = "CaseClassIngredientInteraction",
      inputIngredients = Seq(initialIngredient),
      output = Seq(Event[CaseClassIngredientInteractionSuccessful]))

  trait CaseClassIngredientInteraction {
    val name: String = "CaseClassIngredientInteraction"

    def apply(initialIngredient: String): CaseClassIngredientInteractionSuccessful
  }

  val caseClassIngredientInteraction2 =
    Interaction(
      name = "CaseClassIngredientInteraction2",
      inputIngredients = Seq(caseClassIngredient),
      output = Seq(emptyEvent))

  trait CaseClassIngredientInteraction2 {
    val name: String = "CaseClassIngredientInteraction2"

    def apply(caseClassIngredient: CaseClassIngredient): EmptyEvent
  }

  val NonMatchingReturnTypeInteraction =
    Interaction(
      name="NonMatchingReturnTypeInteraction",
      inputIngredients = Seq(initialIngredient),
      output = Seq(eventFromInteractionTwo))

  trait NonMatchingReturnTypeInteraction {
    val name: String = "NonMatchingReturnTypeInteraction"

    def apply(initialIngredient: String): EventFromInteractionTwo
  }

  val optionalIngredientInteraction =
    Interaction(
      name = "OptionalIngredientInteraction",
      inputIngredients = Seq(
        missingJavaOptional,
        missingJavaOptional2,
        missingScalaOptional,
        missingScalaOptional2,
        initialIngredient),
      output = Seq.empty)

  trait OptionalIngredientInteraction {
    val name: String = "OptionalIngredientInteraction"

    def apply(missingJavaOptional: Optional[String],
              missingJavaOptional2: Optional[Integer],
              missingScalaOptional: Option[String],
              missingScalaOptional2: Option[Integer],
              initialIngredient: String)
  }

  def getRecipe(recipeName: String): Recipe =
    Recipe(recipeName)
      .withInteractions(
        interactionOne
          .withEventOutputTransformer(interactionOneSuccessful, Map("interactionOneOriginalIngredient" -> "interactionOneIngredient"))
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
}
