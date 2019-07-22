package webshop

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.runtime.scaladsl.{Baker, RecipeInformation}
import com.typesafe.config.{Config, ConfigFactory}

object Tmp {

implicit val actorSystem: ActorSystem = ActorSystem("WebshopSystem")

implicit val materializer: Materializer = ActorMaterializer()

val config: Config = ConfigFactory.load()

val baker: Baker = Baker.akka(config, actorSystem, materializer)


}
