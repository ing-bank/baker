package webshop.webservice

import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.typesafe.scalalogging.LazyLogging

object Main extends App with LazyLogging {
  RemoteBakerEventListener.load(event => {
    println(Console.YELLOW + event + Console.RESET)
    logger.info(event.toString)
  })
}
