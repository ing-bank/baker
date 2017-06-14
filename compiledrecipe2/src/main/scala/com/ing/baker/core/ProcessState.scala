package com.ing.baker.core

case class ProcessState(id: java.util.UUID, ingredients: Map[String, Any]) extends InternalBakerData