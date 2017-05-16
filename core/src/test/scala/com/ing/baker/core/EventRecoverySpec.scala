package com.ing.baker.core

import com.ing.baker.api.Event
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.core.EventRecovery._
import com.ing.baker.java_api.{FiresEvent, ProcessId, ProvidesIngredient, RequiresIngredient}
import com.ing.baker.scala_api.{InteractionDescriptorFactory, SRecipe}
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
