package com.ing.baker.runtime.core

import com.ing.baker._

import scala.concurrent.duration._

class BakerTestUtilSpec extends TestRecipeHelper {

  implicit val actorSystem = defaultActorSystem

  "be able to continue a process from a provided list of events" ignore {

    implicit val timeout: FiniteDuration = 2 seconds

    // TODO we need property based testing here and generate the event list for many recipes
    val baker = setupBakerWithRecipe("ProvidedEventList")

    import com.ing.baker.core.EventRecovery._

    val history: List[EventRecovery.Event] = List(
      event(InitialEvent("foo")),
      interaction[InteractionOne]("bar"),
      interaction[InteractionTwo](EventFromInteractionTwo("baz"))
    )

    val processId = java.util.UUID.randomUUID()

    BakerTestUtil.provisionProcessWithEvents(processId, baker.compiledRecipe, history)

    baker.getIngredients(processId) shouldBe Map(
      "initialIngredient"        -> "foo",
      "interactionOneIngredient" -> "bar",
      "interactionTwoIngredient" -> "baz"
    )

    baker.events(processId) shouldBe Seq(InitialEvent("foo"), EventFromInteractionTwo("baz"))
  }
}
