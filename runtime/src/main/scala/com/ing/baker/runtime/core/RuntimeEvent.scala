package com.ing.baker.runtime.core


case class RuntimeEvent(name: String,
                        providedIngredients: Map[String, Any])
