package examples.scala.application

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.inmemory.InMemoryBaker
import com.ing.baker.runtime.model.InteractionInstance
import com.ing.baker.runtime.scaladsl.EventInstance
import examples.scala.events.OrderPlaced
import examples.scala.ingredients.Address
import examples.scala.interactions.{CancelOrderImpl, CheckStockImpl, ShipOrderImpl}
import examples.scala.recipes.WebShopRecipe

import java.util.UUID
import scala.concurrent.duration.DurationInt

class WebShopApp {
  def main(args: Array[String]): Unit = {

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
      _ <- bakerF.fireSensoryEventAndAwaitReceived(recipeInstanceId, sensoryEvent)
      _ <- bakerF.awaitCompleted(recipeInstanceId, timeout = 5.seconds)
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
