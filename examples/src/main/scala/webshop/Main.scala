package webshop

import java.util.concurrent.Future

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.common.EventResult
import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

object Main extends App {

  implicit val actorSystem: ActorSystem =
    ActorSystem("WebshopSystem")
  implicit val materializer: Materializer =
    ActorMaterializer()
  val baker: Baker = Baker.akkaLocalDefault(actorSystem, materializer)

  val FirstOrderPlaced: EventInstance =
    EventInstance.unsafeFrom(WebshopRecipeReflection.OrderPlaced("order-uuid", List("item1", "item2")))
  val recipeInstanceId: String = "recipe id from previously baked recipe instance"

  val result = Future[EventResult] = baker.fireEventAndResolveWhenCompleted(recipeInstanceId, FirstOrderPlaced)
}
