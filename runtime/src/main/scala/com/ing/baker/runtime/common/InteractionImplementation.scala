package com.ing.baker.runtime.common

import com.ing.baker.il.EventDescriptor
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.types.{Type, Value}

import scala.concurrent.Future

/**
  * Provides an implementation for an interaction.
  */
trait InteractionImplementation {

  /**
    * The name of the interaction
    */
  val name: String

  /**
    * The required input.
    */
  val inputTypes: Seq[Type]

  val optionalOutputEvents: Option[Set[EventDescriptor]] = None

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  def execute(input: Seq[Value]): Future[Option[RuntimeEvent]]
}
