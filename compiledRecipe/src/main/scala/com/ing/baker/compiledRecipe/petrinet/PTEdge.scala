package com.ing.baker.compiledRecipe.petrinet

case class PTEdge[T](weight: Long, filter: T ⇒ Boolean)
