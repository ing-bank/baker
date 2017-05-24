package com.ing.baker.runtime.core

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.common.{Event, Interaction}
import com.ing.baker.recipe.javadsl.{FiresEvent, ProcessId, ProvidesIngredient, RequiresIngredient}
import com.ing.baker.recipe.scaladsl.{InteractionDescriptorFactory, SRecipe}
import com.ing.baker.runtime.core.EventRecovery._
import org.scalatest.{Matchers, WordSpecLike}

case class TestEvent(testIngredient: String) extends Event

trait TestInteractionOne extends Interaction {
  @ProvidesIngredient("testInteractionOneIngredient")
  def apply(@ProcessId id: String, @RequiresIngredient("testIngredient") message: String): String
}

case class EventFromTestInteractionTwo(number: Int)

trait TestInteractionTwo extends Interaction {
  @FiresEvent(oneOf = Array(classOf[EventFromTestInteractionTwo]))
  def apply(@RequiresIngredient("testIngredient") message: String): EventFromTestInteractionTwo
}

class EventRecoverySpec extends WordSpecLike with Matchers {

  val testRecipe = SRecipe(
    name = "test",
    interactions = Seq(InteractionDescriptorFactory[TestInteractionOne](),
                       InteractionDescriptorFactory[TestInteractionTwo]()),
    events = Set(classOf[TestEvent])
  )

  val compiledRecipe = RecipeCompiler.compileRecipe(testRecipe)

  val history = List(
    event(TestEvent("foo")),
    interaction[TestInteractionOne]("bar"),
    interaction[TestInteractionTwo](EventFromTestInteractionTwo(123))
  )

  val recoveredEvents =
    transformToKageraEvents(java.util.UUID.randomUUID(), history, compiledRecipe)

  println(recoveredEvents)
}
