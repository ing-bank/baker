package webshop

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp}
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.{Config, ConfigFactory}
import webshop.simple.SimpleWebshopRecipeReflection.PaymentMade

import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object Main extends IOApp {

  val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
  val materializer: Materializer =
    ActorMaterializer()(actorSystem)
  val config: Config =
    ConfigFactory.load()
  val baker: Baker =
    Baker.akkaLocalDefault(actorSystem, materializer)

  override def run(args: List[String]): IO[ExitCode] = ???


  /*
  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(WebshopRecipeReflection.recipe)

  val firstOrderPlaced: EventInstance =
    EventInstance.unsafeFrom(WebshopRecipeReflection.OrderPlaced("order-uuid", List("item1", "item2")))
  val paymentMade: EventInstance =
    EventInstance.unsafeFrom(PaymentMade())
  val paymentMadeExpectedEvents = Seq(
    WebshopRecipe.Events.PaymentMade.name,
    WebshopRecipe.Events.ItemsReserved.name
  )
  val stateExpectedEvents = Seq(
    WebshopRecipe.Events.OrderPlaced.name,
    WebshopRecipe.Events.PaymentMade.name,
    WebshopRecipe.Events.ItemsReserved.name
  )

  val program: Future[Unit] = for {
    _ <- baker.addInteractionInstace(WebshopInstancesReflection.reserveItemsInstance)
    _ <- baker.registerEventListener((recipeInstanceId: String, event: EventInstance) => {
      println(s"Recipe instance : $recipeInstanceId processed event ${event.name}")
    })
    _ <- baker.registerBakerEventListener {
      case e: EventReceived => println(e)
      case e: EventRejected => println(e)
      case e: InteractionFailed => println(e)
      case e: InteractionStarted => println(e)
      case e: InteractionCompleted => println(e)
      case e: ProcessCreated => println(e)
      case e: RecipeAdded => println(e)
    }
    recipeId <- baker.addRecipe(compiledRecipe)
    _ <- baker.bake(recipeId, "first-instance-id")
    _ <- baker.fireEventAndResolveWhenCompleted("first-instance-id", firstOrderPlaced)
    result <- baker.fireEventAndResolveWhenCompleted("first-instance-id", paymentMade)
    state <- baker.getRecipeInstanceState("first-instance-id")
    _ = assert(result.events == paymentMadeExpectedEvents)
    _ = assert(state.events.map(_.name) == stateExpectedEvents)
    visualization <- baker.getVisualState("first-instance-id")
    _ = println(visualization)
  } yield ()

  Await.result(program, 5.seconds)
  */

}
