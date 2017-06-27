package com.ing.baker.il

import com.ing.baker.il.petrinet.{Node, Place, RecipePetriNet, Transition}
import io.kagera.api._
import io.kagera.dot.{GraphDot, PetriNetDot}

import scala.language.higherKinds
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot.{DotAttr, _}
import scalax.collection.io.dot.implicits._

object RecipeVisualizer {

  type RecipePetriNetGraph = BiPartiteGraph[Place[_], Transition[_, _], WLDiEdge]

  private val ingredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("color", "\"#FF6200\""),
    DotAttr("style", "filled")
  )

  private val missingIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
//    DotAttr("fillcolor", "\"#FF6200\""),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  private val eventTransitionAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#767676\"")
  )

  private val eventTransitionFiredAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#3b823a\"")
  )

  private val eventTransitionMissingAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
//    DotAttr("fillcolor", "\"#767676\""),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  private val interactionAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#525199\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )

  private val choiceAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.3),
    DotAttr("height", 0.3)
  )

  private val emptyEventAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.1),
    DotAttr("height", 0.1)
  )

  private val preconditionORAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("fontcolor", "black"),
    DotAttr("label", "OR"),
    DotAttr("style", "filled")
  )

  private val sieveAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#7594d6\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )

  private val attrStmts = List(
    DotAttrStmt(
      Elem.node,
      List(DotAttr("fontname", "ING Me"), DotAttr("fontsize", 22), DotAttr("fontcolor", "white")))
  )

  private val rootAttrs = List(
    DotAttr("pad", 0.2D)
  )

  private def nodeLabelFn: Either[Place[_], Transition[_, _]] ⇒ String = {
    case Left(place) if place.isEmptyEventIngredient  ⇒ s"empty:${place.label}"
    case Left(place)  ⇒ place.label
    case Right(transition) if transition.isMultiFacilitatorTransition ⇒ s"multi:${transition.label}"
    case Right(transition) => transition.label
  }

  private def nodeDotAttrFn: (RecipePetriNetGraph#NodeT, Seq[String])=> List[DotAttr] =
    (node: RecipePetriNetGraph#NodeT, events: Seq[String]) ⇒
      node.value match {
        case Left(place) if place.isInteractionEventOutput    => choiceAttributes
        case Left(place) if place.isOrEventPrecondition       => preconditionORAttributes
        case Left(place) if place.isEmptyEventIngredient      ⇒ emptyEventAttributes
        case Left(place) if node.incomingTransitions.isEmpty  => missingIngredientAttributes
        case Left(place)                                      ⇒ ingredientAttributes
        case Right(transition) if transition.isMultiFacilitatorTransition => choiceAttributes
        case Right(transition) if transition.isInteraction      ⇒ interactionAttributes
        case Right(transition) if transition.isSieve            ⇒ sieveAttributes
        case Right(transition) if transition.isEventMissing     ⇒ eventTransitionMissingAttributes
        case Right(transition) if events.contains(transition.label) ⇒ eventTransitionFiredAttributes
        case Right(transition)                                  ⇒ eventTransitionAttributes
    }

  private def generateDot(graph: RecipePetriNetGraph, filter: String => Boolean, events: Seq[String]): String = {
    val myRoot = DotRootGraph(directed = graph.isDirected,
                              id = None,
                              attrStmts = attrStmts,
                              attrList = rootAttrs)

    def myNodeTransformer(innerNode: RecipePetriNetGraph#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(nodeLabelFn(innerNode.value), nodeDotAttrFn(innerNode, events))))
    }

    def myEdgeTransformer(innerEdge: RecipePetriNetGraph#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {

      val source = innerEdge.edge.source
      val target = innerEdge.edge.target

      Some((myRoot, DotEdgeStmt(nodeLabelFn(source.value), nodeLabelFn(target.value), List.empty)))
    }

    /**
      * Removes a node from the graph & connecting all the adjacent nodes directly to each other.
      */
    def compactNode(graph: RecipePetriNetGraph,
                    node: RecipePetriNetGraph#NodeT): RecipePetriNetGraph = {
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
          WLDiEdge[Node, String](Right(incomingNode), Right(t))(0, ""))

        // Remove the incoming edge and node, combine outgoing edge and newly created edge, remove the outgoing edge and add the new one.
        (outgoingEdges zip newEdges).foldLeft(graph - node - incomingEdge) {
          case (acc, (outgoingEdge, newEdge)) => acc - outgoingEdge + newEdge
        }
      }
    }

    val formattedGraph = graph.nodes.foldLeft(graph) {
      case (graphAccumulator, node) =>
        node.value match {
          case Left(place) if !(place.isIngredient | place.isEmptyEventIngredient | place.isOrEventPrecondition) => compactNode(graphAccumulator, node)
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

  def visualiseCompiledRecipe(compiledRecipe: CompiledRecipe, filter: String => Boolean = s => true, events: Seq[String] = Seq.empty) =
    generateDot(compiledRecipe.petriNet.innerGraph, filter, events)

  def visualisePetrinetOfCompiledRecipe(petriNet: RecipePetriNet) =
    GraphDot.generateDot(petriNet.innerGraph, PetriNetDot.petriNetTheme[Place[_], Transition[_, _]])
}
