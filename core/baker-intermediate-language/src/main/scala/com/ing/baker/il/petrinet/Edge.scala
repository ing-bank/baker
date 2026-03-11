package com.ing.baker.il.petrinet

case class Edge(eventAllowed: Option[String]) {

  def isAllowed(e: Any): Boolean = eventAllowed match {
    case None => true
    case Some(event) => event.equals(e)
  }
}
