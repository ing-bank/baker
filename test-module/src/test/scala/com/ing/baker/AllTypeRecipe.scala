package com.ing.baker

import com.ing.baker.recipe.common.{FiresOneOfEvents, ProvidesIngredient, ProvidesNothing}
import com.ing.baker.recipe.scaladsl._

/** This recipe is mend for testing purposes.
  *
i  * If you need a recipe that makes more sense then see the example package
  *
  * @see com.ing.baker.Examples
  */

object AllTypeRecipe {

  case class User(name: String)

  case class Payload(data: Map[String, String],
                     userMap: Map[String, Int])

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

  val optionalIngredient = Ingredient[Some[String]]
  val listIngredient = Ingredient[List[String]]
  val mapIngredient = Ingredient[Map[String, String]]

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
    output = FiresOneOfEvents(emptyEvent, otherEvent)
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

  // recipe

  val recipe =
    Recipe("AllTypeRecipe")
        .withInteractions(
          interactionThree,
          interactionTwo,
          interactionThree,
          interactionFour,
          interactionFive
            .withRequiredEvent(byteArrayEvent),
          interactionSix,
          interactionSeven
        ).withSensoryEvent(bigPayloadEvent)



  // Byte

  val byteInteraction = Interaction(
    name = "byteInteraction",
    inputIngredients = javaByteIngredient,
    output = ProvidesNothing
  )

  val byteRecipe = Recipe("ByteRecipe").withInteraction(byteInteraction)

  // Short

  val shortInteraction = Interaction(
    name = "shortInteraction",
    inputIngredients = javaShortIngredient,
    output = ProvidesNothing
  )

  val shortRecipe = Recipe("ShortRecipe").withInteraction(shortInteraction)
}
