package com.ing.baker.recipe.scaladsl

import com.ing.baker.TestRecipeHelper
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.annotations.{FiresEvent, RequiresIngredient}
import com.ing.baker.recipe.common.{Event, Interaction}
import com.ing.baker.recipe.newscaladsl.RecipeImplicits._
import com.ing.baker.recipe.newscaladsl.newRecipe._
import com.ing.baker.recipe.scaladsl.testRecipe._

case class AgreementAccepted() extends Event

object NameProvided{
  def apply() = {
    new NameProvided("")
  }
}
case class NameProvided(customerName: String) extends Event
case class CustomerCreated(customerId: String) extends Event
case class AccountOpened(accountId: String) extends Event


trait CreateCustomer extends Interaction {
  @FiresEvent(oneOf = Array(classOf[CustomerCreated]))
  def apply(@RequiresIngredient("customerName") name: String): Event
}

trait OpenAccount extends Interaction {
  @FiresEvent(oneOf = Array(classOf[AccountOpened]))
  def apply(@RequiresIngredient("customerId") customerId: String): Event
}

object testRecipe {
  val oldslRecipe = SRecipe(
    name = "onboard_customer",
    interactions = Seq(
      InteractionDescriptorFactory[CreateCustomer]
        .withRequiredEvent[AgreementAccepted],
      InteractionDescriptorFactory[OpenAccount]
    ),
    events = Set(
      classOf[NameProvided],
      classOf[AgreementAccepted]
    )
  )

  val newdslRecipe =
    "Onboarding_Customer"
      .withInteractions(
        of[CreateCustomer]()
          .withRequiredEvent[AgreementAccepted],
        of[OpenAccount]())
      .withEvents(
        NameProvided(),
        AgreementAccepted())
}

class testRecipe extends TestRecipeHelper {
  "the recipe dsl should" should {

    "compile for the old recipe dsl" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(oldslRecipe)
      System.out.println(compiledRecipe.getRecipeVisualization)
      compiledRecipe.validationErrors shouldBe empty
    }

    "compile for the new recipe dsl" in {
      val compiledRecipe = RecipeCompiler.compileRecipe(newdslRecipe)
      System.out.println(compiledRecipe.getRecipeVisualization)
      compiledRecipe.validationErrors shouldBe empty
    }
  }
}
