package com.ing.baker.runtime.core

import com.ing.baker.il.types.Value

case class ProcessState(processId: String, ingredients: Map[String, Value]) extends Serializable