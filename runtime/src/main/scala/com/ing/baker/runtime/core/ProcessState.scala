package com.ing.baker.runtime.core

case class ProcessState(processId: String, ingredients: Map[String, Any]) extends Serializable