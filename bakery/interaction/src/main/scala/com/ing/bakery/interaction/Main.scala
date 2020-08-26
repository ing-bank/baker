package com.ing.bakery.interaction

import com.ing.baker.runtime.scaladsl.InteractionInstance
import kamon.Kamon

import scala.concurrent.ExecutionContext.Implicits.global

/**
  * Expects single argument containing comma-separated list of interactions' entry points
  */
object Main extends App {

  Kamon.init()

  def getImplementations(classNames: String): List[InteractionInstance] = {
    val interactions: List[String] = classNames.split(",").toList
    interactions
      .map(entryClassName => Class.forName(entryClassName).getConstructor().newInstance().asInstanceOf[AnyRef])
      .map(implementation => InteractionInstance.unsafeFrom(implementation))
  }

  private def runApp(classNames: String): Unit =
    try {
      RemoteInteractionLoader.apply(getImplementations(classNames))
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the classes $classNames", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Please provide comma-separated class names as a parameter"))
}
