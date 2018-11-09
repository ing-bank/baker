package com.ing.baker

import com.ing.baker.recipe.common.InteractionFailureStrategy
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.{UntilDeadline, UntilMaximumRetries}
import com.ing.baker.recipe.scaladsl._
import org.joda.time.{DateTime, LocalDate, LocalDateTime}

import scala.concurrent.duration.DurationInt

/** This recipe is meant for testing purposes.
  *
  * If you need a recipe that makes more sense then see the example package
  *
  * @see com.ing.baker.Examples
  */
object AllTypeRecipe {

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
    inputIngredients = Seq(bigPayloadIngredient),
    output = Seq(javaDataEvent)
  )

  val interactionTwo = Interaction(
    name = "interactionTwo",
    inputIngredients = Seq(javaBooleanIngredient, javaByteIngredient),
    output = Seq(byteArrayEvent, otherEvent)
  )

  val interactionThree = Interaction(
    name = "interactionThree",
    inputIngredients = Seq(bigPayloadIngredient, javaByteIngredient),
    output = Seq(emptyEvent, otherEvent, mapEvent)
  )

  val interactionFour = Interaction(
    name = "interactionFour",
    inputIngredients = Seq(javaIntegerIngredient),
    output = Seq(jodaEvent)
  )

  val interactionFive = Interaction(
    name = "interactionFive",
    inputIngredients = Seq.empty,
    output = Seq(emptyEvent)
  )

  val interactionSix = Interaction(
    name = "interactionSix",
    inputIngredients = Seq(jodaLocalDateIngredient),
    output = Seq()
  )

  val interactionSeven = Interaction(
    name = "interactionSeven",
    inputIngredients = Seq(javaIntegerIngredient),
    output = Seq(scalaDataEvent)
  )

  val sieveInteraction = Interaction(
    name = "sieveInteraction",
    inputIngredients = Seq(javaIntegerIngredient),
    output = Seq(scalaDataEvent)
  )

  val allTypesInteraction = Interaction(
    name = "allTypesInteraction",
    inputIngredients = Seq(bigPayloadIngredient, javaBooleanIngredient, javaByteIngredient, javaShortIngredient, javaCharacterIngredient, javaIntegerIngredient,
      javaLongIngredient, javaFloatIngredient, javaDoubleIngredient, javaStringIngredient, javaBigDecimalIngredient, javaBigIntegerIngredient, byteArrayIngredient,
      jodaDateTimeIngredient, jodaLocalDateIngredient, jodaLocalDateTimeIngredient, booleanIngredient, byteIngredient, shortIngredient, charIngredient, intIngredient,
      longIngredient, floatIngredient, doubleIngredient, stringIngredient, bigDecimalIngredient, bigIntIngredient, optionalIngredient, optionalIngredientForNone,
      primitiveOptionalIngredient, listIngredient, mapIngredient, mapIngredientWithPrimitives, mapIngredientWithBoxedTypes),
    output = Seq(emptyEvent)
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
          .withRequiredOneOfEvents(mapEvent, otherEvent),
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
        sieveInteraction,
        allTypesInteraction.withPredefinedIngredients(
          bigPayloadIngredient(Payload(Map("stringKey" -> "stringValue"), Map("someOtherStringKey" -> java.lang.Integer.MAX_VALUE))),
          javaBooleanIngredient(java.lang.Boolean.TRUE),
          javaByteIngredient(java.lang.Byte.MAX_VALUE),
          javaShortIngredient(java.lang.Short.MAX_VALUE),
          javaCharacterIngredient(java.lang.Character.MAX_VALUE),
          javaIntegerIngredient(java.lang.Integer.MAX_VALUE),
          javaLongIngredient(java.lang.Long.MAX_VALUE),
          javaFloatIngredient(java.lang.Float.MAX_VALUE),
          javaDoubleIngredient(java.lang.Double.MAX_VALUE),
          javaStringIngredient("Some String"),
          javaBigDecimalIngredient(java.math.BigDecimal.valueOf(4.2)),
          javaBigIntegerIngredient(java.math.BigInteger.TEN),
          byteArrayIngredient("some byte array".getBytes),
          jodaDateTimeIngredient(DateTime.now()),
          jodaLocalDateIngredient(LocalDate.now()),
          jodaLocalDateTimeIngredient(LocalDateTime.now()),
          booleanIngredient(true),
          byteIngredient(Byte.MinValue),
          shortIngredient(Short.MinValue),
          charIngredient(Char.MinValue),
          intIngredient(Int.MinValue),
          longIngredient(Long.MinValue),
          floatIngredient(Float.MinValue),
          doubleIngredient(Double.MinValue),
          stringIngredient(""),
          bigDecimalIngredient(BigDecimal(1.2)),
          bigIntIngredient(BigInt(Int.MaxValue)),
          optionalIngredient(Some("some string")),
          optionalIngredientForNone(None),
          primitiveOptionalIngredient(Some(42)),
          listIngredient(List("str1", "str2")),
          mapIngredient(Map("key1" -> "value1")),
          mapIngredientWithPrimitives(Map("key1" -> 42)),
          mapIngredientWithBoxedTypes(Map("key1" -> Int.box(42)))
        )
      )
      .withSensoryEvents(bigPayloadEvent, mapEvent)
      .withEventReceivePeriod(1 minute)
      .withRetentionPeriod(5 minutes)
}
