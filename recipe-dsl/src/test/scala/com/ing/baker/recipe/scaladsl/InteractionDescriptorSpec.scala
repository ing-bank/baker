package com.ing.baker.recipe.scaladsl

import com.ing.baker.recipe.common.ProvidesIngredient
import com.ing.baker.recipe.scaladsl.InteractionDescriptorSpec._
import org.scalatest.{Matchers, WordSpecLike}

object InteractionDescriptorSpec {
  val customerName = Ingredient[String]("customerName")
  val customerId = Ingredient[String]("customerId")
  val createCustomer = Interaction(
    name = "CreateCustomer",
    inputIngredients = Seq(customerName),
    output = ProvidesIngredient(customerId)
  )
  val agreementsAcceptedEvent = Event("agreementsAccepted")
}

class InteractionDescriptorSpec extends WordSpecLike with Matchers {
  "an InteractionDescriptor" when {
    "constructed" should {
      "be valid when using the factory" in {
        val interactionDescriptor: InteractionDescriptor = InteractionDescriptorFactory(createCustomer)
        interactionDescriptor.interaction shouldBe createCustomer
        interactionDescriptor.requiredEvents shouldBe empty
        interactionDescriptor.requiredOneOfEvents shouldBe empty
        interactionDescriptor.predefinedIngredients shouldBe empty
        interactionDescriptor.overriddenIngredientNames shouldBe empty
        interactionDescriptor.overriddenOutputIngredientName shouldBe empty
        interactionDescriptor.maximumInteractionCount shouldBe None
        interactionDescriptor.failureStrategy shouldBe None
        interactionDescriptor.eventOutputTransformers shouldBe empty
      }

      "be valid when using implicit from Interaction" in {
        val interactionDescriptor: InteractionDescriptor = createCustomer
        interactionDescriptor.interaction shouldBe createCustomer
        interactionDescriptor.requiredEvents shouldBe empty
        interactionDescriptor.requiredOneOfEvents shouldBe empty
        interactionDescriptor.predefinedIngredients shouldBe empty
        interactionDescriptor.overriddenIngredientNames shouldBe empty
        interactionDescriptor.overriddenOutputIngredientName shouldBe empty
        interactionDescriptor.maximumInteractionCount shouldBe None
        interactionDescriptor.failureStrategy shouldBe None
        interactionDescriptor.eventOutputTransformers shouldBe empty
      }
    }

    "requiredEvents called" should {
      "update the requiredEventsList" in {
        val updated = createCustomer.withRequiredEvent(agreementsAcceptedEvent)
        updated.requiredEvents shouldBe Set(agreementsAcceptedEvent)
      }
    }
  }
}
