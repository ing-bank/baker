package com.ing.baker.baas.interaction

import com.ing.baker.runtime.scaladsl.InteractionInstance
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * Expects single argument containing full classpath entry point for interaction
 */
object Main extends App {
  private def runApp(classNames: String): Unit =
    try {
      val interactions: List[String] = classNames.split(",").toList
      val implementations = interactions
        .map(entryClassName => Class.forName(entryClassName).newInstance.asInstanceOf[AnyRef])
        .map(implementation => InteractionInstance.unsafeFrom(implementation))
      RemoteInteractionLoader.apply(implementations)
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the classes $classNames", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Please provide comma-separated class names as a parameter"))
}