package com.ing.baker.runtime.core

case class ProcessState(id: String, ingredients: Map[String, Any]) extends Serializable