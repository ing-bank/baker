package webshop.webservice

import akka.actor.ActorSystem
import com.ing.baker.baas.scaladsl.RemoteEventListener
import com.typesafe.scalalogging.LazyLogging

object Main extends App with LazyLogging {

  val actorSystem = ActorSystem("BaaS") // TODO: This should be done by the BaaSInteractionInstance ecosystem to ease the configuration and improve the UX
  val ecosystem = RemoteEventListener(actorSystem)

  ecosystem.registerEventListener("Webshop", (metadata, event) => {
    logger.info("%s [%s] %s", metadata.recipeName, metadata.recipeInstanceId, event.name)
  })
}
