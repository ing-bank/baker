package com.ing.baker.baas.interaction.spring

import java.util

import com.ing.baker.baas.interaction.RemoteInteractionLoader
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.scaladsl.InteractionInstance
import kamon.Kamon
import org.springframework.context.annotation.AnnotationConfigApplicationContext

import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * Expects single argument containing Spring configuration
 */
object Main extends App {

  Kamon.init()

  def getImplementations(configurationClassString: String) : List[InteractionInstance] = {
    val configClass = Class.forName(configurationClassString)
    val ctx = new AnnotationConfigApplicationContext();
    ctx.register(configClass)
    ctx.refresh()
    val interactions: util.Map[String, Interaction] =
      ctx.getBeansOfType(classOf[com.ing.baker.recipe.javadsl.Interaction])
    interactions.asScala.values.map(implementation => InteractionInstance.unsafeFrom(implementation)).toList
  }

  private def runApp(configurationClassString: String): Unit =
    try {
      RemoteInteractionLoader.apply(getImplementations(configurationClassString))
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the interaction instances", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Please provide a Spring configuration containing valid interactions"))
}
