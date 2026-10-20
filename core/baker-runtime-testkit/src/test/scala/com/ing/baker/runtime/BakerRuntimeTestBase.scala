package com.ing.baker.runtime

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.CaseClassIngredient
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.{Recipe => CommonRecipe}
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import com.ing.baker.types.{Converters, Value}
import org.mockito.ArgumentMatchers._
import org.mockito.Mockito._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AsyncWordSpecLike
import org.scalatest.{BeforeAndAfter, BeforeAndAfterAll}
import org.scalatestplus.mockito.MockitoSugar

import java.util.UUID
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
  protected val testInteractionOneWithMetaDataMock: InteractionOneWithMetaData = mock[InteractionOneWithMetaData]
  protected val testInteractionOneWithEventListMock: InteractionOneWithEventList = mock[InteractionOneWithEventList]
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
  protected val testTimerInteractionMock: TimerInteraction = mock[TimerInteraction]

  protected val mockImplementations: List[InteractionInstance] =
    List(
      testInteractionOneMock,
      testInteractionOneWithMetaDataMock,
      testInteractionOneWithEventListMock,
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
      testProvidesNothingInteractionMock,
      testTimerInteractionMock).map(InteractionInstance.unsafeFrom(_))

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

  protected def setupBakerWithRecipe(recipeName: String): Future[(Baker, String)] = {
    val newRecipeName = s"$recipeName-${UUID.randomUUID().toString}"
    setupMockResponse()
    setupBakerWithRecipe(getRecipe(newRecipeName), mockImplementations)
  }

  protected def setupBakerWithRecipe(recipe: CommonRecipe, implementations: List[InteractionInstance]): Future[(Baker, String)] = {
    setupBakerWithoutRecipe(implementations).flatMap { baker =>
      baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe))).map(baker -> _)(ExecutionContext.global)
    }
  }

  protected def setupBakerWithoutRecipe(): Future[Baker] =
    setupBakerWithoutRecipe(mockImplementations)

  protected def setupBakerWithoutRecipe(implementations: List[InteractionInstance]): Future[Baker]
}