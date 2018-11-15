package com.ing.baker.petrinet

import scalax.collection.Graph
import scalax.collection.GraphPredef._
import scalax.collection.edge.WLDiEdge

package object api extends MultiSetOps with MarkingOps {

  /**
    * Identifier type for elements.
    */
  type Id = Long

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
  type Marking[P] = Map[P, MultiSet[Any]]

  /**
    * Type alias for a petri net graph.
    *
    * See also: scala-graph (https://github.com/scala-graph/scala-graph
    */
  type PetriNetGraph[P, T] = Graph[Either[P, T], WLDiEdge]

  implicit class IdentifiableOps[T : Identifiable](e: T) {

    def getId: Long = implicitly[Identifiable[T]].apply(e)
  }

  implicit class IdentifiableSeqOps[T : Identifiable](seq: Iterable[T]) {
    def findById(id: Long): Option[T] = seq.find(e ⇒ implicitly[Identifiable[T]].apply(e) == id)
    def getById(id: Long, name: String = "element"): T = findById(id).getOrElse { throw new IllegalStateException(s"No $name found with id: $id") }
  }

  implicit class MarkingMarshall[P : Identifiable](marking: Marking[P]) {

    def marshall: Marking[Id] = translateKeys(marking, (p: P) => implicitly[Identifiable[P]].apply(p))
  }

  implicit class MarkingUnMarshall(marking: Marking[Id]) {

    def unmarshall[P : Identifiable](places: Iterable[P]): Marking[P] = translateKeys(marking, (id: Long) => places.getById(id, "place in petrinet"))
  }

  def translateKeys[K1, K2, V](map: Map[K1, V], fn: K1 => K2): Map[K2, V] = map.map { case (key, value) ⇒ fn(key) -> value }

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

