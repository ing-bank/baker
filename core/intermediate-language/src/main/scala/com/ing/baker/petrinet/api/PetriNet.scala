package com.ing.baker.petrinet.api

import com.ing.baker.il.petrinet.{Place, Transition}

/**
 * Petri net class.
  *
 * Backed by a graph object from scala-graph (https://github.com/scala-graph/scala-graph)
 */
class PetriNet(val innerGraph: PetriNetGraph) {

  /**
    * The set of places of the petri net
    *
    * @return The set of places
    */
  val places: Set[Place] = innerGraph.nodes.collect { case n if n.isPlace => n.asPlace }.toSet

  /**
    * The set of transitions of the petri net
    *
    * @return The set of transitions.
    */
  val transitions: Set[Transition] = innerGraph.nodes.collect { case n if n.isTransition => n.asTransition }.toSet

  /**
    * The out-adjecent places of a transition.
    *
    * @param t transition
    * @return
    */
  def outgoingPlaces(t: Transition): Set[Place] = innerGraph.get(Right(t)).outgoingPlaces

  /**
    * The out-adjacent transitions of a place.
    *
    * @param p place
    * @return
    */
  def outgoingTransitions(p: Place): Set[Transition] = innerGraph.get(Left(p)).outgoingTransitions

  /**
    * The in-adjacent places of a transition.
    *
    * @param t transition
    * @return
    */
  def incomingPlaces(t: Transition): Set[Place] = innerGraph.get(Right(t)).incomingPlaces

  /**
    * The in-adjacent transitions of a place.
    *
    * @param p place
    * @return
    */
  def incomingTransitions(p: Place): Set[Transition] = innerGraph.get(Left(p)).incomingTransitions

  /**
    * The set of nodes (places + transitions) in the petri net.
    *
    * @return The set of nodes.
    */
  def nodes: scala.collection.Set[Either[Place, Transition]] = innerGraph.nodes.map(_.value)

  /**
    * Returns the in-marking of a transition. That is; a map of place -> arc weight
    *
    * @param t transition
    * @return
    */
  def inMarking(t: Transition): MultiSet[Place] = innerGraph.get(Right(t)).incoming.map(e => e.source.asPlace -> e.weight.toInt).toMap

  /**
    * The out marking of a transition. That is; a map of place -> arc weight
    *
    * @param t transition
    * @return
    */
  def outMarking(t: Transition): MultiSet[Place] = innerGraph.get(Right(t)).outgoing.map(e => e.target.asPlace -> e.weight.toInt).toMap

  /**
    * Returns the (optional) edge for a given place -> transition pair.
    *
    * @param from The source place.
    * @param to The target transition.
    * @return
    */
  def findPTEdge(from: Place, to: Transition): Option[Any] =
    innerGraph.get(Left(from)).outgoing.find(_.target.value == Right(to)).map(_.toOuter.label)

  /**
    * Returns the (optional) edge for a given transition -> place pair.
    *
    * @param from The source transition.
    * @param to The target place.
    * @return
    */
  def findTPEdge(from: Transition, to: Place): Option[Any] =
    innerGraph.get(Right(from)).outgoing.find(_.target.value == Left(to)).map(_.toOuter.label)

  /**
    * We override the hashCode function since the scalax.collections.Graph hashCode is non deterministic
    */
  override val hashCode = {

    innerGraph.edges.map(e => (e.source.value, e.target.value, e.weight, e.label)).toSet.hashCode
  }

  override def equals(obj: Any) = {

    obj match {
      case null => false
      case pn: PetriNet => pn.innerGraph.equals(innerGraph)
      case _ => false
    }
  }
}