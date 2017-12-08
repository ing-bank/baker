package com.ing.baker.il.petrinet

case class EventNameFilter(name: String) extends (Any => Boolean) {
  override def apply(s: Any) = s == name
}

case object NoFilter extends (Any => Boolean) {
  override def apply(s: Any) = true
}

case class PTEdge[T](weight: Long, filter: T ⇒ Boolean)
