package webshop

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object Main extends App {

  implicit val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
  implicit val materializer: Materializer =
    ActorMaterializer()
  val baker: Baker = Baker.akkaLocalDefault(actorSystem, materializer)

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipe.recipe)

  val program: Future[Unit] = for {
    _ <- baker.addImplementation(WebshopInstancesReflection.reserveItemsInstance)
    recipeId <- baker.addRecipe(compiledRecipe)
    _ <- baker.bake(recipeId, "first-instance-id")
    firstOrderPlaced: EventInstance =
      EventInstance.unsafeFrom(WebshopRecipeReflection.OrderPlaced("order-uuid", List("item1", "item2")))
    result <- baker.fireEventAndResolveWhenCompleted("first-instance-id", firstOrderPlaced)
    state <- baker.getProcessState("first-instance-id")
    expectedEvents = Seq(WebshopRecipe.Events.OrderPlaced.name, WebshopRecipe.Events.ItemsReserved.name)
    _ = assert(result.events == expectedEvents)
    _ = assert(state.events.map(_.name) == expectedEvents)
    visualization <- baker.getVisualState("first-instance-id")
    _ = println(visualization)
  } yield ()

  Await.result(program, 5.seconds)
}
