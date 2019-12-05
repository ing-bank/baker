package webshop.webservice

import akka.actor.ActorSystem
import akka.management.cluster.bootstrap.ClusterBootstrap
import akka.management.scaladsl.AkkaManagement
import com.ing.baker.baas.scaladsl.BaaSEventListener
import org.slf4j.LoggerFactory

object Main extends App {

  val log = LoggerFactory.getLogger("EventListener")

  val actorSystem = ActorSystem("BaaS") // This should be done by the BaaSInteractionInstance ecosystem to ease the configuration and improve the UX
  AkkaManagement(actorSystem).start()
  ClusterBootstrap(actorSystem).start()
  val ecosystem = BaaSEventListener(actorSystem)

  ecosystem.registerEventListener("Webshop", (metadata, event) => {
    log.info(metadata.recipeName + " [" + metadata.recipeInstanceId + "] " + event.name)
  })
}
