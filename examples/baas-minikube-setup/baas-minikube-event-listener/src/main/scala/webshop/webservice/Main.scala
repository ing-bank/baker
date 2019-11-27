package webshop.webservice

import akka.actor.ActorSystem
import akka.management.cluster.bootstrap.ClusterBootstrap
import akka.management.scaladsl.AkkaManagement
import com.ing.baker.baas.scaladsl.BaaSEventListener

object Main extends App {

  val actorSystem = ActorSystem("BaaS") // This should be done by the BaaSInteractionInstance ecosystem to ease the configuration and improve the UX
  AkkaManagement(actorSystem).start()
  ClusterBootstrap(actorSystem).start()
  val ecosystem = BaaSEventListener(actorSystem)

  ecosystem.registerEventListener("Webshop", (metadata, event) => {
    println(metadata.recipeName + " [" + metadata.recipeInstanceId + "] " + event.name)
  })
}
