package webshop.simple

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should.Matchers

import java.util.UUID
import scala.concurrent.{ExecutionContext, Future}

class WebshopRecipeSpec extends AsyncFlatSpec with Matchers  {

  "The WebshopRecipeReflection" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(SimpleWebshopRecipeReflection.recipe)
    Future.successful(succeed)
  }

  "The WebshopRecipe" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(SimpleWebshopRecipe.recipe)
    Future.successful(succeed)
  }

  it should "visualize the recipe" in {
    val compiled = RecipeCompiler.compileRecipe(SimpleWebshopRecipe.recipe)
    val viz: String = compiled.getRecipeVisualization
    println(Console.GREEN + s"Recipe visualization, paste this into webgraphviz.com:")
    println(viz + Console.RESET)
    Future.successful(succeed)
  }

  trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[SimpleWebshopRecipeReflection.ReserveItemsOutput]
  }

  class ReserveItemsMock extends ReserveItems {

    override def apply(orderId: String, items: List[String]): Future[SimpleWebshopRecipeReflection.ReserveItemsOutput] = {

      // Http call to the Warehouse service
      val response: Future[Either[List[String], List[String]]] =
      // This is mocked for the sake of the example
        Future.successful(Right(items))

      // Build an event instance that Baker understands
      response.map {
        case Left(unavailableItems) =>
          SimpleWebshopRecipeReflection.OrderHadUnavailableItems(unavailableItems)
        case Right(reservedItems) =>
          SimpleWebshopRecipeReflection.ItemsReserved(reservedItems)
      }
    }
  }

  it should "reserve items in happy conditions" in {
    val system: ActorSystem = ActorSystem("baker-webshop-system")
    implicit val cs: ContextShift[IO] = IO.contextShift(ExecutionContext.global)

    val reserveItemsInstance: InteractionInstance =
      InteractionInstance.unsafeFrom(new ReserveItemsMock)
    val baker: Baker = AkkaBaker.localDefault(system, CachingInteractionManager(reserveItemsInstance))

    val compiled = RecipeCompiler.compileRecipe(SimpleWebshopRecipe.recipe)
    val recipeInstanceId: String = UUID.randomUUID().toString

    val orderId: String = "order-id"
    val items: List[String] = List("item1", "item2")

    val orderPlaced = EventInstance
      .unsafeFrom(SimpleWebshopRecipeReflection.OrderPlaced(orderId, items))
    val paymentMade = EventInstance
      .unsafeFrom(SimpleWebshopRecipeReflection.PaymentMade())


    for {
      recipeId <- baker.addRecipe(RecipeRecord.of(compiled))
      _ <- baker.bake(recipeId, recipeInstanceId)
      _ <- baker.fireEventAndResolveWhenCompleted(
        recipeInstanceId, orderPlaced)
      _ <- baker.fireEventAndResolveWhenCompleted(
        recipeInstanceId, paymentMade)
      state <- baker.getRecipeInstanceState(recipeInstanceId)
      provided = state
        .ingredients
        .find(_._1 == "reservedItems")
        .map(_._2.as[List[String]])
        .map(_.mkString(", "))
        .getOrElse("No reserved items")

    } yield provided shouldBe items.mkString(", ")
  }
}
