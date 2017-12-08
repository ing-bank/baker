package com.ing.baker.runtime.core

import com.ing.baker.types.Value

case class ProcessState(processId: String, ingredients: Map[String, Value]) extends Serializable