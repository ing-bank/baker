package webshop.webservice

import akka.actor.ActorSystem
import cats.effect.IO
import com.ing.baker.baas.scaladsl.RemoteInteraction
import com.ing.baker.runtime.scaladsl.InteractionInstance

object Main extends App {

  val actorSystem = ActorSystem("BaaS") // This should be done by the BaaSInteractionInstance ecosystem to ease the configuration and improve the UX
  val ecosystem = RemoteInteraction(actorSystem)
  val timer = IO.timer(actorSystem.dispatcher)

  import actorSystem.dispatcher

  val instances = InteractionInstance.unsafeFromList(List(
    new MakePaymentInstance()(timer),
    new ReserveItemsInstance()(timer),
    new ShipItemsInstance()(timer)
  ))

  ecosystem.load(instances: _*)
}
