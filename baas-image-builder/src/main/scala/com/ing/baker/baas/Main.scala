package com.ing.baker.baas

import com.ing.baker.baas.scaladsl.RemoteInteraction
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.concurrent.ExecutionContext.Implicits.global

/**
  * Expects single argument containing full classpath entry point for interaction
  */
object Main extends App {
  private def runApp(entryClassName: String): Unit =
    try {
      val implementation = Class.forName(entryClassName).newInstance.asInstanceOf[AnyRef]
      RemoteInteraction.load(InteractionInstance.unsafeFrom(implementation))
    } catch {
      case ex: Exception =>
        throw new IllegalStateException(s"Unable to initialize the class name $entryClassName", ex)
    }

  args.headOption.map(runApp).getOrElse(throw new IllegalAccessException("Expected class name a parameter"))
}