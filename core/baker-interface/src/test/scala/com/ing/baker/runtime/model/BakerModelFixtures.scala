package com.ing.baker.runtime.model

import cats.Applicative
import cats.effect.Sync
import com.ing.baker.runtime.scaladsl.{EventInstance, InteractionInstance, InteractionInstanceF}
import com.ing.baker.types.{Converters, Value}
import org.mockito.Matchers.anyString
import org.mockito.Mockito.when
import org.scalatestplus.mockito.MockitoSugar

import scala.reflect.ClassTag

trait BakerModelFixtures[F[_]] extends TestRecipe[F] with MockitoSugar {

  val initialIngredientValue = "initialIngredient"
  val sievedIngredientValue = "sievedIngredient"
  val interactionOneOriginalIngredientValue = "interactionOneOriginalIngredient"
  val interactionOneIngredientValue = "interactionOneIngredient"
  val interactionTwoIngredientValue = "interactionTwoIngredient"
  val interactionTwoEventValue = EventFromInteractionTwo(interactionTwoIngredientValue)
  val interactionThreeIngredientValue = "interactionThreeIngredient"
  val interactionFourIngredientValue = "interactionFourIngredient"
  val interactionFiveIngredientValue = "interactionFiveIngredient"
  val interactionSixIngredientValue = "interactionSixIngredient"
  val caseClassIngredientValue = CaseClassIngredient(5, "this is a case class test")
  val errorMessage = "This is the error message"

  def ingredientMap(entries: (String, Any)*): Map[String, Value] =
    entries.map { case (name, obj) => name -> Converters.toValue(obj) }.toMap

  def eventList(events: Any*): Seq[EventInstance] = events.map(EventInstance.unsafeFrom)

  //Can be used to check the state after firing the initialEvent
  val afterInitialState = ingredientMap(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue
  )

  //Can be used to check the state after firing the initialEvent and SecondEvent
  val finalState = ingredientMap(
    "initialIngredient" -> initialIngredientValue,
    "sievedIngredient" -> sievedIngredientValue,
    "interactionOneIngredient" -> interactionOneIngredientValue,
    "interactionTwoIngredient" -> interactionTwoIngredientValue,
    "interactionThreeIngredient" -> interactionThreeIngredientValue,
    "interactionFourIngredient" -> interactionFourIngredientValue
  )

  val testInteractionOneMock: InteractionOne = mock[InteractionOne]
  val testInteractionTwoMock: InteractionTwo = mock[InteractionTwo]
  val testInteractionThreeMock: InteractionThree = mock[InteractionThree]
  val testInteractionFourMock: InteractionFour = mock[InteractionFour]
  val testInteractionFiveMock: InteractionFive = mock[InteractionFive]
  val testInteractionSixMock: InteractionSix = mock[InteractionSix]
  val testFireTwoEventsInteractionMock: fireTwoEventsInteraction = mock[fireTwoEventsInteraction]
  val testComplexIngredientInteractionMock: ComplexIngredientInteraction = mock[ComplexIngredientInteraction]
  val testCaseClassIngredientInteractionMock: CaseClassIngredientInteraction = mock[CaseClassIngredientInteraction]
  val testCaseClassIngredientInteraction2Mock: CaseClassIngredientInteraction2 = mock[CaseClassIngredientInteraction2]
  val testNonMatchingReturnTypeInteractionMock: NonMatchingReturnTypeInteraction = mock[NonMatchingReturnTypeInteraction]
  val testSieveInteractionMock: SieveInteraction = mock[SieveInteraction]
  val testOptionalIngredientInteractionMock: OptionalIngredientInteraction = mock[OptionalIngredientInteraction]
  val testProvidesNothingInteractionMock: ProvidesNothingInteraction = mock[ProvidesNothingInteraction]

  def mockImplementations(implicit effect: Applicative[F], classTag: ClassTag[F[Any]]): Seq[InteractionInstanceF[F]] =
    Seq(
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
      testProvidesNothingInteractionMock).map(InteractionInstanceF.unsafeFrom[F](_))

  protected def setupMockResponse(implicit effect: Sync[F]): F[Unit] = effect.delay {
    when(testInteractionOneMock.apply(anyString(), anyString())).thenReturn(effect.pure(InteractionOneSuccessful(interactionOneIngredientValue)))
    when(testInteractionTwoMock.apply(anyString())).thenReturn(interactionTwoEventValue)
    when(testInteractionThreeMock.apply(anyString(), anyString())).thenReturn(InteractionThreeSuccessful(interactionThreeIngredientValue))
    when(testInteractionFourMock.apply()).thenReturn(InteractionFourSuccessful(interactionFourIngredientValue))
    when(testInteractionFiveMock.apply(anyString(), anyString(), anyString())).thenReturn(InteractionFiveSuccessful(interactionFiveIngredientValue))
    when(testInteractionSixMock.apply(anyString())).thenReturn(InteractionSixSuccessful(interactionSixIngredientValue))
    when(testSieveInteractionMock.apply(anyString(), anyString())).thenReturn(SieveInteractionSuccessful(sievedIngredientValue))
  }

}
