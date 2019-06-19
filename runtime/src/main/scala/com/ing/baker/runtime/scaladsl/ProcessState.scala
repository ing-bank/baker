package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.types.Value

import scala.collection.JavaConverters._

/**
  * Holds the 'state' of a process instance.
  *
  * @param processId   The process identifier
  * @param ingredients The accumulated ingredients
  * @param eventNames  The names of the events occurred so far
  */
case class ProcessState(
    processId: String,
    ingredients: Map[String, Value],
    events: Seq[RuntimeEvent])
  extends common.ProcessState with ScalaApi {

  type EventType = RuntimeEvent

  def eventNames: Seq[String] = events.map(_.name)

  def asJava: javadsl.ProcessState =
    new javadsl.ProcessState(processId, ingredients.asJava, events.map(_.asJava).asJava)
}
