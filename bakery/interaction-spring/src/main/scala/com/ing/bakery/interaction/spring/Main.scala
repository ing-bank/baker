package com.ing.bakery.interaction.spring

import java.util

import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.interaction.RemoteInteractionLoader
import com.typesafe.scalalogging.LazyLogging
import org.springframework.context.annotation.AnnotationConfigApplicationContext

import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * Expects single argument containing Spring configuration
 */
object Main extends App with LazyLogging{

  def getImplementations(configurationClassString: String) : List[InteractionInstance] = {
    val configClass = Class.forName(configurationClassString)
    logger.info("Class found: " + configClass)
    val ctx = new AnnotationConfigApplicationContext();
    logger.info("Context created")
    ctx.register(configClass)
    logger.info("Context registered")
    ctx.refresh()
    logger.info("Context refreshed")
    val interactions: util.Map[String, Interaction] =
      ctx.getBeansOfType(classOf[com.ing.baker.recipe.javadsl.Interaction])
    interactions.asScala.values.map(implementation => {
      val instance = InteractionInstance.unsafeFrom(implementation)
      logger.info("Added implementation: " + instance.name)
      instance
    }).toList
  }

  private def runApp(configurationClassString: String): Unit =
    try {
      logger.info("Starting for configuration: " + configurationClassString)
      val implementations = getImplementations(configurationClassString)
      logger.info("Starting RemoteInteractionLoader")
      RemoteInteractionLoader(implementations)
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the interaction instances", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Please provide a Spring configuration containing valid interactions"))
}
