package com.ing.baker.petrinet

import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.edge.WLDiEdge

package object api extends MultiSetOps with MarkingOps {

  case class Id(value: Long) extends AnyVal

  /**
    * Type alias for something that is identifiable.
    */
  type Identifiable[T] = T ⇒ Id

  /**
    * Type alias for a multi set.
    */
  type MultiSet[T] = Map[T, Int]

  /**
    * Type alias for a marking.
    */
  type Marking[P[_]] = HMap[P, MultiSet]

  /**
    * Type alias for a single marked place, meaning a place containing tokens.
    *
    * @tparam T the type of tokens the place can hold.
    */
  type MarkedPlace[P[_], T] = (P[T], MultiSet[T])

  implicit class IdentifiableOps[T : Identifiable](seq: Iterable[T]) {
    def findById(id: Long): Option[T] = seq.find(e ⇒ implicitly[Identifiable[T]].apply(e).value == id)
    def getById(id: Long, name: String = "element"): T = findById(id).getOrElse { throw new IllegalStateException(s"No $name found with id: $id") }
  }

  type PetriNetGraph[P, T] = Graph[Either[P, T], WLDiEdge]

  implicit def placeToNode[P, T](p: P): Either[P, T] = Left(p)
  implicit def transitionToNode[P, T](t: T): Either[P, T] = Right(t)

  implicit class PetriNetGraphNodeOps[P, T](val node: PetriNetGraph[P, T]#NodeT) {

    def asPlace: P = node.value match {
      case Left(p) ⇒ p
      case _       ⇒ throw new IllegalStateException(s"node $node is not a place!")
    }

    def asTransition: T = node.value match {
      case Right(t) ⇒ t
      case _        ⇒ throw new IllegalStateException(s"node $node is not a transition!")
    }

    def incomingNodes: Set[Either[P, T]] = node.incoming.map(_.source.value)
    def incomingPlaces: Set[P] = incomingNodes.collect { case Left(place) => place }
    def incomingTransitions: Set[T] = incomingNodes.collect { case Right(transition) => transition }

    def outgoingNodes: Set[Either[P, T]] = node.outgoing.map(_.target.value)
    def outgoingPlaces: Set[P] = outgoingNodes.collect { case Left(place) => place }
    def outgoingTransitions: Set[T] = outgoingNodes.collect { case Right(transition) => transition }

    def isPlace: Boolean = node.value.isLeft
    def isTransition: Boolean = node.value.isRight
  }
}

