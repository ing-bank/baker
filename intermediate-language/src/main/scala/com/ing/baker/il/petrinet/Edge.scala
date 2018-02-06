package com.ing.baker.il.petrinet

case class Edge[T](eventAllowed: Option[String]) {
  def isAllowed(e: T): Boolean = eventAllowed match {
    case None => true
    case Some(event) => event.equals(e)
  }
}
