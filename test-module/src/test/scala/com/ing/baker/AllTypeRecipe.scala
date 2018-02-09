package com.ing.baker

import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.{UntilDeadline, UntilMaximumRetries}
import com.ing.baker.recipe.common.{FiresOneOfEvents, InteractionFailureStrategy, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.types.{Converters, Value}
import org.joda.time.{DateTime, LocalDate, LocalDateTime}

import scala.concurrent.duration.DurationInt

/** This recipe is meant for testing purposes.
  *
  * If you need a recipe that makes more sense then see the example package
  *
  * @see com.ing.baker.Examples
  */

object AllTypeRecipe {

  implicit class IngredientOps[T](ingredient: Ingredient[T]) {
    def instance(e: T): (String, Value) = {
      val value = Converters.toValue(e)
      (ingredient.name, value)
    }
  }

  case class Payload(data: Map[String, String], userData: Map[String, java.lang.Integer])

  // ingredients

  val bigPayloadIngredient = Ingredient[Payload]
  val javaBooleanIngredient = Ingredient[java.lang.Boolean]
  val javaByteIngredient = Ingredient[java.lang.Byte]
  val javaShortIngredient = Ingredient[java.lang.Short]
  val javaCharacterIngredient = Ingredient[java.lang.Character]
  val javaIntegerIngredient = Ingredient[java.lang.Integer]
  val javaLongIngredient = Ingredient[java.lang.Long]
  val javaFloatIngredient = Ingredient[java.lang.Float]
  val javaDoubleIngredient = Ingredient[java.lang.Double]
  val javaStringIngredient = Ingredient[java.lang.String]
  val javaBigDecimalIngredient = Ingredient[java.math.BigDecimal]
  val javaBigIntegerIngredient = Ingredient[java.math.BigInteger]
  val byteArrayIngredient = Ingredient[Array[Byte]]
  val jodaDateTimeIngredient = Ingredient[org.joda.time.DateTime]
  val jodaLocalDateIngredient = Ingredient[org.joda.time.LocalDate]
  val jodaLocalDateTimeIngredient = Ingredient[org.joda.time.LocalDateTime]

  val booleanIngredient = Ingredient[Boolean]
  val byteIngredient = Ingredient[Byte]
  val shortIngredient = Ingredient[Short]
  val charIngredient = Ingredient[Char]
  val intIngredient = Ingredient[Int]
  val longIngredient = Ingredient[Long]
  val floatIngredient = Ingredient[Float]
  val doubleIngredient = Ingredient[Double]
  val stringIngredient = Ingredient[String]
  val bigDecimalIngredient = Ingredient[BigDecimal]
  val bigIntIngredient = Ingredient[BigInt]

  val optionalIngredient = Ingredient[Option[String]]
  val optionalIngredientForNone = Ingredient[Option[String]]
  val primitiveOptionalIngredient = Ingredient[Option[Int]]
  val listIngredient = Ingredient[List[String]]
  val mapIngredient = Ingredient[Map[String, String]]
  val mapIngredientWithPrimitives = Ingredient[Map[String, Int]]
  val mapIngredientWithBoxedTypes = Ingredient[Map[String, java.lang.Integer]]

  // events

  val javaDataEvent = Event(
    javaBooleanIngredient,
    javaByteIngredient,
    javaShortIngredient,
    javaCharacterIngredient,
    javaIntegerIngredient,
    javaLongIngredient,
    javaFloatIngredient,
    javaDoubleIngredient,
    javaStringIngredient,
    javaBigDecimalIngredient,
    javaBigIntegerIngredient
  )
  val scalaDataEvent = Event(
    booleanIngredient,
    byteIngredient,
    shortIngredient,
    charIngredient,
    intIngredient,
    longIngredient,
    floatIngredient,
    doubleIngredient,
    stringIngredient,
    bigDecimalIngredient,
    bigIntIngredient
  )
  val byteArrayEvent = Event(byteArrayIngredient)
  val bigPayloadEvent = Event(bigPayloadIngredient)
  val jodaEvent = Event(jodaDateTimeIngredient, jodaLocalDateIngredient, jodaLocalDateTimeIngredient)
  val otherEvent = Event(optionalIngredient, listIngredient)
  val emptyEvent = Event()
  val mapEvent = Event(mapIngredient, mapIngredientWithPrimitives, mapIngredientWithBoxedTypes)

  // interactions

  val interactionOne = Interaction(
    name = "interactionOne",
    inputIngredients = bigPayloadIngredient,
    output = FiresOneOfEvents(javaDataEvent)
  )

  val interactionTwo = Interaction(
    name = "interactionTwo",
    inputIngredients = Ingredients(javaBooleanIngredient, javaByteIngredient),
    output = FiresOneOfEvents(byteArrayEvent, otherEvent)
  )

  val interactionThree = Interaction(
    name = "interactionThree",
    inputIngredients = Ingredients(bigPayloadIngredient, javaByteIngredient),
    output = FiresOneOfEvents(emptyEvent, otherEvent, mapEvent)
  )

  val interactionFour = Interaction(
    name = "interactionFour",
    inputIngredients = javaIntegerIngredient,
    output = FiresOneOfEvents(jodaEvent)
  )

  val interactionFive = Interaction(
    name = "interactionFive",
    inputIngredients = Seq(),
    output = ProvidesIngredient(javaStringIngredient)
  )

  val interactionSix = Interaction(
    name = "interactionSix",
    inputIngredients = jodaLocalDateIngredient,
    output = ProvidesNothing
  )

  val interactionSeven = Interaction(
    name = "interactionSeven",
    inputIngredients = javaIntegerIngredient,
    output = FiresOneOfEvents(scalaDataEvent)
  )

  val sieveInteraction = Interaction(
    name = "sieveInteraction",
    inputIngredients = javaIntegerIngredient,
    output = FiresOneOfEvents(scalaDataEvent)
  )

  val allTypesInteraction = Interaction(
    name = "allTypesInteraction",
    inputIngredients = Seq(bigPayloadIngredient, javaBooleanIngredient, javaByteIngredient, javaShortIngredient, javaCharacterIngredient, javaIntegerIngredient,
      javaLongIngredient, javaFloatIngredient, javaDoubleIngredient, javaStringIngredient, javaBigDecimalIngredient, javaBigIntegerIngredient, byteArrayIngredient,
      jodaDateTimeIngredient, jodaLocalDateIngredient, jodaLocalDateTimeIngredient, booleanIngredient, byteIngredient, shortIngredient, charIngredient, intIngredient,
      longIngredient, floatIngredient, doubleIngredient, stringIngredient, bigDecimalIngredient, bigIntIngredient, optionalIngredient, optionalIngredientForNone,
      primitiveOptionalIngredient, listIngredient, mapIngredient, mapIngredientWithPrimitives, mapIngredientWithBoxedTypes),
    output = FiresOneOfEvents(emptyEvent)
  )

  // recipe

  val recipe =
    Recipe("AllTypeRecipe")
      .withInteractions(
        interactionTwo,
        interactionThree
          .withEventOutputTransformer(otherEvent, "renamedOtherEvent", Map("optionalIngredient" -> "renamedOptionalIngredient"))
          .withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
            .withInitialDelay(5.seconds)
            .withBackoffFactor(2.0)
            .withUntil(Some(UntilMaximumRetries(10)))
            .withMaxTimeBetweenRetries(Some(100.milliseconds))
            .withFireRetryExhaustedEvent(mapEvent)
            .build()
          )
          .withMaximumInteractionCount(5)
          .withOverriddenIngredientName("longIngredient", "renamedLongIngredient")
          .withRequiredOneOfEvents(mapEvent, otherEvent)
          .withOverriddenOutputIngredientName("renamedIngredient"),
        interactionFour.withFailureStrategy(InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
          .withInitialDelay(5.seconds)
          .withBackoffFactor(2.0)
          .withUntil(Some(UntilDeadline(10.minutes)))
          .withMaxTimeBetweenRetries(Some(100.milliseconds))
          .withFireRetryExhaustedEvent(Some("someEventName"))
          .build()
        ),
        interactionFive
          .withRequiredEvent(byteArrayEvent)
          .withFailureStrategy(InteractionFailureStrategy.FireEventAfterFailure()),
        interactionSix,
        interactionSeven,
        allTypesInteraction.withPredefinedIngredients(
          bigPayloadIngredient.instance(Payload(Map("stringKey" -> "stringValue"), Map("someOtherStringKey" -> java.lang.Integer.MAX_VALUE))),
          javaBooleanIngredient.instance(java.lang.Boolean.TRUE),
          javaByteIngredient.instance(java.lang.Byte.MAX_VALUE),
          javaShortIngredient.instance(java.lang.Short.MAX_VALUE),
          javaCharacterIngredient.instance(java.lang.Character.MAX_VALUE),
          javaIntegerIngredient.instance(java.lang.Integer.MAX_VALUE),
          javaLongIngredient.instance(java.lang.Long.MAX_VALUE),
          javaFloatIngredient.instance(java.lang.Float.MAX_VALUE),
          javaDoubleIngredient.instance(java.lang.Double.MAX_VALUE),
          javaStringIngredient.instance("Some String"),
          javaBigDecimalIngredient.instance(java.math.BigDecimal.valueOf(4.2)),
          javaBigIntegerIngredient.instance(java.math.BigInteger.TEN),
          byteArrayIngredient.instance("some byte array".getBytes),
          jodaDateTimeIngredient.instance(DateTime.now()),
          jodaLocalDateIngredient.instance(LocalDate.now()),
          jodaLocalDateTimeIngredient.instance(LocalDateTime.now()),
          booleanIngredient.instance(true),
          byteIngredient.instance(Byte.MinValue),
          shortIngredient.instance(Short.MinValue),
          charIngredient.instance(Char.MinValue),
          intIngredient.instance(Int.MinValue),
          longIngredient.instance(Long.MinValue),
          floatIngredient.instance(Float.MinValue),
          doubleIngredient.instance(Double.MinValue),
          stringIngredient.instance(""),
          bigDecimalIngredient.instance(BigDecimal(1.2)),
          bigIntIngredient.instance(BigInt(Int.MaxValue)),
          optionalIngredient.instance(Some("some string")),
          optionalIngredientForNone.instance(None),
          primitiveOptionalIngredient.instance(Some(42)),
          listIngredient.instance(List("str1", "str2")),
          mapIngredient.instance(Map("key1" -> "value1")),
          mapIngredientWithPrimitives.instance(Map("key1" -> 42)),
          mapIngredientWithBoxedTypes.instance(Map("key1" -> Int.box(42)))
        )
      )
      .withSensoryEvents(bigPayloadEvent, mapEvent)
      .withEventReceivePeriod(1 minute)
      .withRetentionPeriod(5 minutes)
      .withSieves(sieveInteraction)
}
