package webshop

import java.util.UUID

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}
import org.scalatest.{FlatSpec, Matchers}

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Await
import scala.concurrent.duration._

class WebshopRecipeSpec extends FlatSpec with Matchers {

  val system: ActorSystem = ActorSystem("baker-webshop-system")

  val materializer: Materializer = ActorMaterializer()(system)

  val baker: Baker = Baker.akkaLocalDefault(system, materializer)

  "The WebshopRecipeReflection" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(WebshopRecipeReflection.recipe)
  }

  "The WebshopRecipe" should "compile the recipe without errors" in {
    RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
  }

  it should "visualize the recipe" in {
    val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    val viz: String = compiled.getRecipeVisualization
    println(Console.GREEN + s"Recipe visualization, paste this into webgraphviz.com:")
    println(viz + Console.RESET)
  }

  it should "run the manually mocked interaction" in {
    val compiled = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)
    val recipeInstanceId: String = UUID.randomUUID().toString

    val orderId: String = "order-id"
    val items: List[String] = List("item1", "item2")

    val orderPlaced = EventInstance
      .unsafeFrom(WebshopRecipeReflection.OrderPlaced(orderId, items))
    val paymentMade = EventInstance
      .unsafeFrom(WebshopRecipeReflection.PaymentMade())

    val program = for {
      _ <- baker.addInteractionInstace(WebshopInstances.ReserveItemsInstance)
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
    } yield provided
    val outcome = Await.result(program, 5.seconds)
    outcome shouldBe items.mkString(", ")
  }
}
