package com.ing.baker.petrinet.api

import scalax.collection.edge.WLDiEdge

/**
 * Petri net interface.
 *
 * TODO also incorporate the edge types, P -> T and T -> P ?
 */
trait PetriNet[P, T] {

  /**
   * The scala-graph backing petri net.
   *
   * @return
   */
  def innerGraph: BiPartiteGraph[P, T, WLDiEdge]

  /**
   * The set of places of the petri net
   *
   * @return The set of places
   */
  def places: Set[P]

  /**
   * The set of transitions of the petri net
   *
   * @return The set of transitions.
   */
  def transitions: Set[T]

  /**
   * The out-adjecent places of a transition.
   *
   * @param t transition
   * @return
   */
  def outgoingPlaces(t: T): Set[P]

  /**
   * The out-adjacent transitions of a place.
   *
   * @param p place
   * @return
   */
  def outgoingTransitions(p: P): Set[T]

  /**
   * The in-adjacent places of a transition.
   *
   * @param t transition
   * @return
   */
  def incomingPlaces(t: T): Set[P]

  /**
   * The in-adjacent transitions of a place.
   *
   * @param p place
   * @return
   */
  def incomingTransitions(p: P): Set[T]

  /**
   * Returns the in-marking of a transition. That is; a map of place -> arc weight
   *
   * @param t transition
   * @return
   */
  def inMarking(t: T): MultiSet[P]

  /**
   * The out marking of a transition. That is; a map of place -> arc weight
   *
   * @param t transition
   * @return
   */
  def outMarking(t: T): MultiSet[P]

  /**
   * The set of nodes (places + transitions) in the petri net.
   *
   * @return The set of nodes.
   */
  def nodes: scala.collection.Set[Either[P, T]]
}