package com.ing.baker.petrinet

import com.ing.baker.il.petrinet.{Place, Transition}
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
  type Identifiable[X] = X => Id

  /**
    * Type alias for a multi set.
    */
  type MultiSet[X] = Map[X, Int]

  /**
    * Type alias for a marking.
    */
  type Marking[X] = Map[X, MultiSet[Any]]

  /**
    * Type alias for a petri net graph.
    *
    * See also: scala-graph (https://github.com/scala-graph/scala-graph
    */
  type PetriNetGraph = Graph[Either[Place, Transition], WLDiEdge]

  implicit class IdentifiableOps[X : Identifiable](e: X) {

    def getId: Long = implicitly[Identifiable[X]].apply(e)
  }

  implicit class IdentifiableSeqOps[T : Identifiable](seq: Iterable[T]) {
    def findById(id: Long): Option[T] = seq.find(e => implicitly[Identifiable[T]].apply(e) == id)
    def getById(id: Long, name: String = "element"): T = findById(id).getOrElse { throw new IllegalStateException(s"No $name found with id: $id") }
  }

  implicit class MarkingMarshall(marking: Marking[Place]) {

    def marshall: Marking[Id] = translateKeys(marking, (p: Place) => implicitly[Identifiable[Place]].apply(p))
  }

  implicit class MarkingUnMarshall(marking: Marking[Id]) {

    def unmarshall(places: Iterable[Place]): Marking[Place] = translateKeys(marking, (id: Long) => places.getById(id, "place in petrinet"))
  }

  def translateKeys[K1, K2, V](map: Map[K1, V], fn: K1 => K2): Map[K2, V] = map.map { case (key, value) => fn(key) -> value }

  implicit class PetriNetGraphNodeOps(val node: PetriNetGraph#NodeT) {

    def asPlace: Place = node.value match {
      case Left(p) => p
      case _       => throw new IllegalStateException(s"node $node is not a place!")
    }

    def asTransition: Transition = node.value match {
      case Right(t) => t
      case _        => throw new IllegalStateException(s"node $node is not a transition!")
    }

    def incomingNodes: Set[Either[Place, Transition]] = node.incoming.map(_.source.value)
    def incomingPlaces: Set[Place] = incomingNodes.collect { case Left(place) => place }
    def incomingTransitions: Set[Transition] = incomingNodes.collect { case Right(transition) => transition }

    def outgoingNodes: Set[Either[Place, Transition]] = node.outgoing.map(_.target.value)
    def outgoingPlaces: Set[Place] = outgoingNodes.collect { case Left(place) => place }
    def outgoingTransitions: Set[Transition] = outgoingNodes.collect { case Right(transition) => transition }

    def isPlace: Boolean = node.value.isLeft
    def isTransition: Boolean = node.value.isRight
  }
}

