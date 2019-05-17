package com.ing.baker.runtime.common

import com.ing.baker.types.Value

trait SensoryEventResult[Seq[_], Map[_, _]] {

  def status: SensoryEventStatus

  def events: Seq[String]

  def ingredients: Map[String, Value]
}

