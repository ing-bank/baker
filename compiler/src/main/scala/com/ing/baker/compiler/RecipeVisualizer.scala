package com.ing.baker.compiler

import io.kagera.api._
import io.kagera.api.colored.{Place, Transition}

import scala.language.higherKinds
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot._
import scalax.collection.io.dot.implicits._

object RecipeVisualizer {

  type ColoredPetriNetGraph = BiPartiteGraph[Place[_], Transition[_, _, _], WLDiEdge]

  val ingredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("color", "\"#FF6200\""),
    DotAttr("style", "filled")
  )

  val eventTransitionAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#767676\"")
  )

  val eventTransitionFiredAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#3b823a\"")
  )

  val eventTransitionMissingAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#EE0000\"")
  )

  val interactionAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#525199\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )

  val choiceAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.3),
    DotAttr("height", 0.3)
  )

  val emptyEventAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.1),
    DotAttr("height", 0.1)
  )

  val preconditionORAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("fontcolor", "black"),
    DotAttr("label", "OR"),
    DotAttr("style", "filled")
  )

  val sieveAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#7594d6\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )

  val attrStmts = List(
    DotAttrStmt(
      Elem.node,
      List(DotAttr("fontname", "ING Me"), DotAttr("fontsize", 22), DotAttr("fontcolor", "white")))
  )

  val rootAttrs = List(
    DotAttr("pad", 0.2D)
  )

  def nodeLabelFn: Either[Place[_], Transition[_, _, _]] ⇒ String = {
    case Left(a)  ⇒ a.label
    case Right(b) ⇒ b.label
  }

  def nodeDotAttrFn: (ColoredPetriNetGraph#NodeT, Seq[String])=> List[DotAttr] =
    (node: ColoredPetriNetGraph#NodeT, events: Seq[String]) ⇒
      node.value match {
        case Left(place) if place.isInteractionEventOutput => choiceAttributes
        case Left(place) if place.isOrEventPrecondition    => preconditionORAttributes
        case Left(place) if place.isEmptyEventIngredient   ⇒ emptyEventAttributes
        case Left(place)                                   ⇒ ingredientAttributes
        case Right(transition) if transition.isParallelizationTransition =>
          choiceAttributes // TODO, better way to hide the multiTransition
        case Right(transition) if transition.isInteraction  ⇒ interactionAttributes
        case Right(transition) if transition.isSieve        ⇒ sieveAttributes
        case Right(transition) if transition.isEventMissing ⇒ eventTransitionMissingAttributes
        case Right(transition) if events.contains(transition.label) ⇒ eventTransitionFiredAttributes
        case Right(transition)                              ⇒ eventTransitionAttributes
    }

  implicit class PetriNetVisualization[P, T](graph: ColoredPetriNetGraph) {
    def toDot(filter: String => Boolean): String = RecipeVisualizer.generateDot(graph, filter)
  }

  def generateDot(graph: ColoredPetriNetGraph, filter: String => Boolean, events: Seq[String] = Seq.empty): String = {
    val myRoot = DotRootGraph(directed = graph.isDirected,
                              id = None,
                              attrStmts = attrStmts,
                              attrList = rootAttrs)

    def myNodeTransformer(innerNode: ColoredPetriNetGraph#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(nodeLabelFn(innerNode.value), nodeDotAttrFn(innerNode, events))))
    }

    def myEdgeTransformer(innerEdge: ColoredPetriNetGraph#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {

      val source = innerEdge.edge.source
      val target = innerEdge.edge.target

      Some((myRoot, DotEdgeStmt(nodeLabelFn(source.value), nodeLabelFn(target.value), List.empty)))
    }

    /**
      * Removes a node from the graph & connecting all the adjacent nodes directly to each other.
      */
    def compactNode(graph: ColoredPetriNetGraph,
                    node: ColoredPetriNetGraph#NodeT): ColoredPetriNetGraph = {
      //There is no input node so remove node
      if (node.incomingTransitions.isEmpty) graph - node
      //There is a input node so link incoming and outgoing together
      else {
        // The node coming into the transition
        val incomingNode = node.incomingTransitions.head

        // Get the incoming edge (there is only one per definition of the result edge
        val incomingEdge = node.incoming.head

        // Get the outgoing edges and transitions
        val outgoingEdges = node.outgoing
        val outgoingTransitions = node.outgoingTransitions

        // Create new edges from incoming to outgoing transition
        val newEdges = outgoingTransitions.map(t =>
          WLDiEdge[colored.Node, String](Right(incomingNode), Right(t))(0, ""))

        // Remove the incoming edge and node, combine outgoing edge and newly created edge, remove the outgoing edge and add the new one.
        (outgoingEdges zip newEdges).foldLeft(graph - node - incomingEdge) {
          case (acc, (outgoingEdge, newEdge)) => acc - outgoingEdge + newEdge
        }
      }
    }

    val formattedGraph = graph.nodes.foldLeft(graph) {
      case (graphAccumulator, node) =>
        node.value match {
          case Left(place) if !place.isIngredient => compactNode(graphAccumulator, node)
          case _                                  => graphAccumulator
        }
    }

    val filteredGraph = graph.nodes.foldLeft(formattedGraph) {
      case (graphAccumulator, edge) =>
        if (filter(edge.toString)) {
          graphAccumulator
        } else {
          graphAccumulator - edge
        }
    }

    graph2DotExport(filteredGraph).toDot(dotRoot = myRoot,
                                         edgeTransformer = myEdgeTransformer,
                                         cNodeTransformer = Some(myNodeTransformer))
  }
}
