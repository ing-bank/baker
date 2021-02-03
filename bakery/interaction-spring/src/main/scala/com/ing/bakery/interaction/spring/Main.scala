package com.ing.bakery.interaction.spring

import java.util
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.interaction.RemoteInteractionLoader
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import org.springframework.context.annotation.AnnotationConfigApplicationContext

import java.io.File
import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * Expects single argument containing Spring configuration
 */
object Main extends App with LazyLogging{

  def implementations(configurationClassString: String) : List[InteractionInstance] = {

    def forClass(c: String) = {
      val configClass = Class.forName(c)
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

    configurationClassString
      .split(',')
      .map(forClass)
      .toList.flatten
  }

  private def runApp(configurationClassString: String): Unit =
    try {
      logger.info(s"Starting RemoteInteractionLoader")
      RemoteInteractionLoader(implementations(configurationClassString))
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the interaction instances", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Please provide a Spring configuration containing valid interactions"))
}
