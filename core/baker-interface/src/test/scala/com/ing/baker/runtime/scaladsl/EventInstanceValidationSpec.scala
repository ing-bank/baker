package com.ing.baker.runtime.scaladsl

import com.ing.baker.il.{EventDescriptor, IngredientDescriptor}
import com.ing.baker.types
import com.ing.baker.types._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec

/**
 * Isolated unit tests for EventInstance validation logic.
 * 
 * These tests were created to test EventInstance.validate() method in isolation,
 * without requiring full actor infrastructure or integration setup. This provides
 * faster feedback and clearer test coverage for validation business logic.
 * 
 * The validation logic is used in ProcessIndex actor to validate sensory events
 * before they are fired to process instances.
 */
class EventInstanceValidationSpec extends AnyWordSpec with Matchers {

  "EventInstance.validate" should {

    "return no errors when event matches descriptor perfectly" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("orderId", types.CharArray),
          IngredientDescriptor("amount", types.Int32)
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "orderId" -> PrimitiveValue("order-123"),
          "amount" -> PrimitiveValue(100)
        )
      )

      val errors = event.validate(descriptor)
      errors shouldBe empty
    }

    "return error when event name doesn't match descriptor" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq.empty
      )

      val event = EventInstance(
        name = "PaymentReceived",
        providedIngredients = Map.empty
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("Provided event with name 'PaymentReceived' does not match expected name 'OrderPlaced'")
    }

    "return error when required ingredient is missing" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("orderId", types.CharArray),
          IngredientDescriptor("amount", types.Int32)
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "orderId" -> PrimitiveValue("order-123")
          // Missing "amount"
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("no value was provided for ingredient 'amount'")
    }

    "return error when ingredient has null value for non-optional type" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("orderId", types.CharArray), // Non-optional
          IngredientDescriptor("notes", types.OptionType(types.CharArray)) // Optional
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "orderId" -> NullValue,
          "notes" -> NullValue // This is OK - it's optional
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("null is not allowed for non optional ingredient 'orderId'")
    }

    "allow null value for optional ingredient" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("orderId", types.CharArray),
          IngredientDescriptor("notes", types.OptionType(types.CharArray))
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "orderId" -> PrimitiveValue("order-123"),
          "notes" -> NullValue
        )
      )

      val errors = event.validate(descriptor)
      errors shouldBe empty
    }

    "return error when ingredient has incorrect type" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("amount", types.Int32)
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "amount" -> PrimitiveValue("not-a-number") // String instead of Int32
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("ingredient 'amount' has an incorrect type")
    }

    "return multiple errors when multiple ingredients are invalid" in {
      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("orderId", types.CharArray),
          IngredientDescriptor("amount", types.Int32),
          IngredientDescriptor("customerId", types.CharArray)
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "orderId" -> PrimitiveValue("order-123")
          // Missing "amount" and "customerId"
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 2
      errors should contain("no value was provided for ingredient 'amount'")
      errors should contain("no value was provided for ingredient 'customerId'")
    }

    "validate complex types correctly" in {
      val recordType = types.RecordType(Seq(
        types.RecordField("street", types.CharArray),
        types.RecordField("city", types.CharArray),
        types.RecordField("zipCode", types.CharArray)
      ))

      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("shippingAddress", recordType)
        )
      )

      val validAddress = RecordValue(Map(
        "street" -> PrimitiveValue("123 Main St"),
        "city" -> PrimitiveValue("Springfield"),
        "zipCode" -> PrimitiveValue("12345")
      ))

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "shippingAddress" -> validAddress
        )
      )

      val errors = event.validate(descriptor)
      errors shouldBe empty
    }

    "return error when complex type is missing required fields" in {
      val recordType = types.RecordType(Seq(
        types.RecordField("street", types.CharArray),
        types.RecordField("city", types.CharArray)
      ))

      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("shippingAddress", recordType)
        )
      )

      val invalidAddress = RecordValue(Map(
        "street" -> PrimitiveValue("123 Main St")
        // Missing "city"
      ))

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "shippingAddress" -> invalidAddress
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("ingredient 'shippingAddress' has an incorrect type")
      errors.head should include("city")
    }

    "validate list types correctly" in {
      val listType = types.ListType(types.CharArray)

      val descriptor = EventDescriptor(
        name = "OrderPlaced",
        ingredients = Seq(
          IngredientDescriptor("itemNames", listType)
        )
      )

      val event = EventInstance(
        name = "OrderPlaced",
        providedIngredients = Map(
          "itemNames" -> ListValue(List(
            PrimitiveValue("item1"),
            PrimitiveValue("item2"),
            PrimitiveValue("item3")
          ))
        )
      )

      val errors = event.validate(descriptor)
      errors shouldBe empty
    }

    "validate enum types correctly" in {
      val enumType = types.EnumType(Set("PENDING", "CONFIRMED", "CANCELLED"))

      val descriptor = EventDescriptor(
        name = "OrderStatusChanged",
        ingredients = Seq(
          IngredientDescriptor("status", enumType)
        )
      )

      val event = EventInstance(
        name = "OrderStatusChanged",
        providedIngredients = Map(
          "status" -> PrimitiveValue("CONFIRMED")
        )
      )

      val errors = event.validate(descriptor)
      errors shouldBe empty
    }

    "return error when enum value is not in allowed set" in {
      val enumType = types.EnumType(Set("PENDING", "CONFIRMED", "CANCELLED"))

      val descriptor = EventDescriptor(
        name = "OrderStatusChanged",
        ingredients = Seq(
          IngredientDescriptor("status", enumType)
        )
      )

      val event = EventInstance(
        name = "OrderStatusChanged",
        providedIngredients = Map(
          "status" -> PrimitiveValue("INVALID_STATUS")
        )
      )

      val errors = event.validate(descriptor)
      errors should have size 1
      errors.head should include("ingredient 'status' has an incorrect type")
    }
  }
}
