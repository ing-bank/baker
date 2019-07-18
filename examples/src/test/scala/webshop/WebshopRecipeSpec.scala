package webshop

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance, InteractionInstance}
import org.scalatest.{AsyncFlatSpec, Matchers}
import org.mockito.Mockito._
import org.scalatest.mockito.MockitoSugar

import scala.concurrent.Future

class WebshopRecipeSpec extends AsyncFlatSpec with Matchers with MockitoSugar {

  "The WebshopRecipeReflection" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(WebshopRecipeReflection.recipe)
    Future.successful(succeed)
  }

  "The WebshopRecipe" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    Future.successful(succeed)
  }

  it should "visualize the recipe" in {
    val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    val viz: String = compiled.getRecipeVisualization
    println(Console.GREEN + s"Recipe visualization, paste this into webgraphviz.com:")
    println(viz + Console.RESET)
    Future.successful(succeed)
  }

  trait ReserveItems {

    def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput]
  }

  class ReserveItemsMock extends ReserveItems {

    override def apply(orderId: String, items: List[String]): Future[WebshopRecipeReflection.ReserveItemsOutput] = {

      // Http call to the Warehouse service
      val response: Future[Either[List[String], List[String]]] =
      // This is mocked for the sake of the example
        Future.successful(Right(items))

      // Build an event instance that Baker understands
      response.map {
        case Left(unavailableItems) =>
          WebshopRecipeReflection.OrderHadUnavailableItems(unavailableItems)
        case Right(reservedItems) =>
          WebshopRecipeReflection.ItemsReserved(reservedItems)
      }
    }
  }

  it should "reserve items in happy conditions" in {

    val system: ActorSystem = ActorSystem("baker-webshop-system")
    val materializer: Materializer = ActorMaterializer()(system)
    val baker: Baker = Baker.akkaLocalDefault(system, materializer)

    val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    val recipeInstanceId: String = UUID.randomUUID().toString

    val orderId: String = "order-id"
    val items: List[String] = List("item1", "item2")

    val orderPlaced = EventInstance
      .unsafeFrom(WebshopRecipeReflection.OrderPlaced(orderId, items))
    val paymentMade = EventInstance
      .unsafeFrom(WebshopRecipeReflection.PaymentMade())

    val reserveItemsInstance: InteractionInstance =
      InteractionInstance.unsafeFrom(new ReserveItemsMock)

    for {
      _ <- baker.addInteractionInstace(reserveItemsInstance)
      recipeId <- baker.addRecipe(compiled)
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

  it should "reserve items in happy conditions (mockito)" in {

    val system: ActorSystem = ActorSystem("baker-webshop-system")
    val materializer: Materializer = ActorMaterializer()(system)
    val baker: Baker = Baker.akkaLocalDefault(system, materializer)

    val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    val recipeInstanceId: String = UUID.randomUUID().toString

    val orderId: String = "order-id"
    val items: List[String] = List("item1", "item2")

    val orderPlaced = EventInstance
      .unsafeFrom(WebshopRecipeReflection.OrderPlaced(orderId, items))
    val paymentMade = EventInstance
      .unsafeFrom(WebshopRecipeReflection.PaymentMade())

    // The ReserveItems interaction being mocked by Mockito
    val mockedReserveItems: ReserveItems = mock[ReserveItems]
    val reserveItemsInstance: InteractionInstance =
      InteractionInstance.unsafeFrom(mockedReserveItems)

    when(mockedReserveItems.apply(orderId, items))
      .thenReturn(Future.successful(WebshopRecipeReflection.ItemsReserved(items)))

    for {
      _ <- baker.addInteractionInstace(reserveItemsInstance)
      recipeId <- baker.addRecipe(compiled)
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

      // Verify that the mock was called with the expected data
      _ = verify(mockedReserveItems).apply(orderId, items)
    } yield provided shouldBe items.mkString(", ")
  }

}
