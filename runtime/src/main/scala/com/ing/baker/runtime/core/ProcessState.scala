package com.ing.baker.runtime.core

case class ProcessState(id: java.util.UUID, ingredients: Map[String, Any]) extends Serializable