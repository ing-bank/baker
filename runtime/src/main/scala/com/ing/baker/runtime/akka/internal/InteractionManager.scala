package com.ing.baker.runtime.akka.internal

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstance}

import scala.concurrent.Future

trait InteractionManager {
  def hasImplementation(interaction: InteractionTransition): Boolean

  def executeImplementation(interaction: InteractionTransition, input: Seq[IngredientInstance]): Future[Option[EventInstance]]

  def addImplementation(interaction: InteractionInstance): Unit
}
