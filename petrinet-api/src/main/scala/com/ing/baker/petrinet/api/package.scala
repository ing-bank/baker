package com.ing.baker.petrinet

import com.esotericsoftware.kryo.io.{Input, Output}
import com.esotericsoftware.kryo.{Kryo, KryoSerializable}

import scala.PartialFunction._
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

  implicit def extractId[T](e: T)(implicit identifiable: Identifiable[T]) = identifiable(e).value

  implicit class IdentifiableOps[T : Identifiable](seq: Iterable[T]) {
    def findById(id: Long): Option[T] = seq.find(e ⇒ implicitly[Identifiable[T]].apply(e).value == id)
    def getById(id: Long, name: String = "element"): T = findById(id).getOrElse { throw new IllegalStateException(s"No $name found with id: $id") }
  }

  implicit class OptionOps(check: Boolean) {
    def option[A](provider: => A): Option[A] =
      if (check)
        Some(provider)
      else
        None
  }

  def requireUniqueElements[T](i: Iterable[T], name: String = "Element"): Unit = {
    (Set.empty[T] /: i) { (set, e) ⇒
      if (set.contains(e))
        throw new IllegalArgumentException(s"$name '$e' is not unique!")
      else
        set + e
    }
  }

  type BiPartiteGraph[P, T, E[X] <: EdgeLikeIn[X]] = Graph[Either[P, T], E]

  /**
    * TODO; can we remove this wrapper? It seems only needed because we need to mix in other traits with PetriNet
    * which cannot be done with Graph.apply
    */
  case class ScalaGraphPetriNet[P, T](val innerGraph: BiPartiteGraph[P, T, WLDiEdge]) extends PetriNet[P, T]  {

    override def inMarking(t: T): MultiSet[P] = innerGraph.inMarking(t)
    override def outMarking(t: T): MultiSet[P] = innerGraph.outMarking(t)
    override def outgoingPlaces(t: T): Set[P] = innerGraph.outgoingPlaces(t)
    override def outgoingTransitions(p: P): Set[T] = innerGraph.outgoingTransitions(p)
    override def incomingPlaces(t: T): Set[P] = innerGraph.incomingPlaces(t)
    override def incomingTransitions(p: P): Set[T] = innerGraph.incomingTransitions(p)

    override lazy val places = innerGraph.places().toSet
    override lazy val transitions = innerGraph.transitions().toSet

    override def nodes: scala.collection.Set[Either[P, T]] = innerGraph.nodes.map(_.value)
  }

  implicit def placeToNode[P, T](p: P): Either[P, T] = Left(p)
  implicit def transitionToNode[P, T](t: T): Either[P, T] = Right(t)

  implicit class PetriNetGraphNodeTAdditions[A, B](val node: BiPartiteGraph[A, B, WLDiEdge]#NodeT) {

    def asPlace: A = node.value match {
      case Left(p) ⇒ p
      case _       ⇒ throw new IllegalStateException(s"node $node is not a place!")
    }

    def asTransition: B = node.value match {
      case Right(t) ⇒ t
      case _        ⇒ throw new IllegalStateException(s"node $node is not a transition!")
    }

    def incomingPlaces = node.incoming.map(_.source.asPlace)
    def incomingTransitions = node.incoming.map(_.source.asTransition)

    def outgoingPlaces = node.outgoing.map(_.target.asPlace)
    def outgoingTransitions = node.outgoing.map(_.target.asTransition)

    def isPlace = cond(node.value) { case Left(n) ⇒ true }
    def isTransition = cond(node.value) { case Right(n) ⇒ true }
  }

  implicit class PetriNetGraphAdditions[P, T](val graph: BiPartiteGraph[P, T, WLDiEdge]) {

    def inMarking(t: T): MultiSet[P] = graph.get(t).incoming.map(e ⇒ e.source.asPlace -> e.weight.toInt).toMap
    def outMarking(t: T): MultiSet[P] = graph.get(t).outgoing.map(e ⇒ e.target.asPlace -> e.weight.toInt).toMap

    def findPTEdge(from: P, to: T): Option[WLDiEdge[Either[P, T]]] =
      graph.get(Left(from)).outgoing.find(_.target.value == Right(to)).map(_.toOuter)

    def findTPEdge(from: T, to: P): Option[WLDiEdge[Either[P, T]]] =
      graph.get(Right(from)).outgoing.find(_.target.value == Left(to)).map(_.toOuter)

    def incomingPlaces(t: T): Set[P] = graph.get(t).incomingPlaces

    def incomingTransitions(p: P): Set[T] = graph.get(p).incomingTransitions

    def outgoingPlaces(t: T): Set[P] = graph.get(t).outgoingPlaces

    def outgoingTransitions(p: P): Set[T] = graph.get(p).outgoingTransitions

    def places() = graph.nodes.collect { case n if n.isPlace ⇒ n.asPlace }

    def transitions() = graph.nodes.collect { case n if n.isTransition ⇒ n.asTransition }
  }
}

