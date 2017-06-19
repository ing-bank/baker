package com.ing.baker.il.petrinet

case class PTEdge[T](weight: Long, filter: T ⇒ Boolean)
