package webshop.webservice

import com.ing.baker.baas.scaladsl.RemoteEventListener
import com.typesafe.scalalogging.LazyLogging

object Main extends App with LazyLogging {
  RemoteEventListener.load((metadata, event) => {
    println(Console.YELLOW + metadata.recipeName + " [" + metadata.recipeInstanceId + "] " + event.name + Console.RESET)
    logger.info(metadata.recipeName + " [" + metadata.recipeInstanceId + "] " + event.name)
  })
}
