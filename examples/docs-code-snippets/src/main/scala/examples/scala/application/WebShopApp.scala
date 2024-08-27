package examples.scala.application

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.compiler.RecipeCompiler
import examples.scala.events.OrderPlaced
import com.ing.baker.runtime.inmemory.InMemoryBaker
import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.scaladsl.EventInstance
import examples.scala.ingredients.Address
import examples.scala.interactions.{CancelOrderImpl, CheckStockImpl, ShipOrderImpl}
import examples.scala.recipes.WebShopRecipe

import java.util.UUID
import scala.concurrent.ExecutionContext

class WebShopApp {
  def main(args: Array[String]): Unit = {

    implicit val timer: Timer[IO] = IO.timer(ExecutionContext.global)
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

    val interactions = List(
      new CancelOrderImpl(),
      new ShipOrderImpl(),
      new CheckStockImpl(),
    )

    val bakerF = InMemoryBaker.build(implementations = interactions.map(InteractionInstance.unsafeFrom[IO]))
      .unsafeRunSync()

    val recipeInstanceId = UUID.randomUUID().toString
    val sensoryEvent = EventInstance.unsafeFrom(orderPlaced)

    for {
      recipeId <- bakerF.addRecipe(RecipeCompiler.compileRecipe(recipe = WebShopRecipe.recipe), validate = true)
      _ <- bakerF.bake(recipeId, recipeInstanceId)
      _ <- bakerF.fireEventAndResolveWhenCompleted(recipeInstanceId, sensoryEvent)

    } yield recipeId
  }

  private val orderPlaced = OrderPlaced(
    orderId = "123",
    customerId = "456",
    productIds = List("iPhone", "PlayStation5"),
    address = Address(
      street = "Hoofdstraat",
      city = "Amsterdam",
      zipCode = "1234AA",
      country = "The Netherlands"
    )
  )
}
