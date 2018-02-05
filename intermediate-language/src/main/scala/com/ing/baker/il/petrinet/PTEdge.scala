package com.ing.baker.il.petrinet

case class PTEdge[T](weight: Long, eventAllowed: Option[String]) {
  def isAllowed(e: T): Boolean = eventAllowed match {
    case None => true
    case Some(event) => event.equals(e)
  }
}
