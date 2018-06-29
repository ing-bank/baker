package com.ing.baker.il

import com.ing.baker.il.petrinet.{InteractionTransition, Node, Place, RecipePetriNet, Transition}
import com.ing.baker.petrinet.api._
import com.typesafe.config.{Config, ConfigFactory}
import dot._

import scala.collection.JavaConverters._
import scala.language.higherKinds
import scalax.collection.Graph
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot.{DotAttr, _}
import scalax.collection.io.dot.implicits._

class RecipeStyle(config: Config) {

  def readAttributes(key: String): List[DotAttr] =
    config.getConfig(key)
      .entrySet().asScala
      .map(e => e.getKey -> e.getValue.unwrapped())
      .toMap.-("shape") // shape is not allowed to be overriden
      .map {
        case (key, s: String) => Some(DotAttr(key, s))
        case (key, n: java.lang.Integer) => Some(DotAttr(key, n.intValue()))
        case (key, n: java.lang.Long) => Some(DotAttr(key, n.longValue()))
        case (key, n: java.lang.Float) => Some(DotAttr(key, n.floatValue()))
        case (key, n: java.lang.Double) => Some(DotAttr(key, n.doubleValue()))
        case other => None
      }.toList.flatten

  val ingredientAttributes: List[DotAttr] =
    DotAttr("shape", "circle") +: readAttributes("ingredient")

  val providedIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("color", "\"#3b823a\""),
    DotAttr("style", "filled")
  )

  val missingIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  val eventAttributes: List[DotAttr] =
    DotAttr("shape", "diamond") +: readAttributes("event")

  val sensoryEventAttributes: List[DotAttr] =
    DotAttr("shape", "diamond") +: readAttributes("sensory-event")

  val interactionAttributes: List[DotAttr] =
    DotAttr("shape", "rect") +: readAttributes("interaction")

  val eventFiredAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#3b823a\"")
  )

  val eventMissingAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  val firedInteractionAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#3b823a\""),
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

  val commonNodeAttributes = List(
    DotAttrStmt(
      Elem.node,
      readAttributes("common")
    ))

  val rootAttrs = List(
    DotAttr("pad", 0.2D)
  )
}

object RecipeVisualizer {

  type RecipePetriNetGraph = Graph[Either[Place[_], Transition[_]], WLDiEdge]

  private def nodeLabelFn: Either[Place[_], Transition[_]] ⇒ String = {
    case Left(place) if place.isEmptyEventIngredient ⇒ s"empty:${place.label}"
    case Left(place) ⇒ place.label
    case Right(transition) if transition.isMultiFacilitatorTransition ⇒ s"multi:${transition.label}"
    case Right(transition) => transition.label
  }

  private def nodeDotAttrFn(style: RecipeStyle): (RecipePetriNetGraph#NodeT, Set[String], Set[String]) => List[DotAttr] =
    (node: RecipePetriNetGraph#NodeT, eventNames: Set[String], ingredientNames: Set[String]) ⇒
      node.value match {
        case Left(place) if place.isInteractionEventOutput => style.choiceAttributes
        case Left(place) if place.isOrEventPrecondition => style.preconditionORAttributes
        case Left(place) if place.isEmptyEventIngredient ⇒ style.emptyEventAttributes
        case Left(_) if node.incomingTransitions.isEmpty => style.missingIngredientAttributes
        case Left(place) if ingredientNames contains place.label ⇒ style.providedIngredientAttributes
        case Left(_) ⇒ style.ingredientAttributes
        case Right(t: InteractionTransition[_]) if eventNames.intersect(t.eventsToFire.map(_.name).toSet).nonEmpty => style.firedInteractionAttributes
        case Right(transition) if eventNames.contains(transition.label) ⇒ style.eventFiredAttributes
        case Right(transition) if transition.isMultiFacilitatorTransition => style.choiceAttributes
        case Right(transition) if transition.isInteraction ⇒ style.interactionAttributes
        case Right(transition) if transition.isSieve ⇒ style.sieveAttributes
        case Right(transition) if transition.isEventMissing ⇒ style.eventMissingAttributes
        case Right(transition) if transition.isSensoryEvent => style.sensoryEventAttributes
        case Right(_) ⇒ style.eventAttributes
      }

  private def generateDot(graph: RecipePetriNetGraph, style: RecipeStyle, filter: String => Boolean, eventNames: Set[String], ingredientNames: Set[String]): String = {
    val myRoot = DotRootGraph(directed = graph.isDirected,
      id = None,
      attrStmts = style.commonNodeAttributes,
      attrList = style.rootAttrs)

    def myNodeTransformer(innerNode: RecipePetriNetGraph#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(nodeLabelFn(innerNode.value), nodeDotAttrFn(style)(innerNode, eventNames, ingredientNames))))
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
          case _ => graphAccumulator
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

  def visualiseCompiledRecipe(compiledRecipe: CompiledRecipe,
                              filter: String => Boolean = _ => true,
                              eventNames: Set[String] = Set.empty,
                              ingredientNames: Set[String] = Set.empty): String = {

    val config = ConfigFactory.load().getConfig("baker.visualization")
    val configuredStyle = config.getString("style")

    val pickedStyle = if (!config.hasPath(s"styles.$configuredStyle")) {
      System.err.println(s"no configuration for recipe style '$configuredStyle' found, falling back to default")
      "default"
    } else
      configuredStyle

    val recipeStyle = new RecipeStyle(config.getConfig(s"styles.$pickedStyle"))

    generateDot(compiledRecipe.petriNet.innerGraph, recipeStyle, filter, eventNames, ingredientNames)
  }

  def visualisePetrinetOfCompiledRecipe(petriNet: RecipePetriNet): String =
    GraphDot.generateDot(petriNet.innerGraph, PetriNetDot.petriNetTheme[Place[_], Transition[_]])
}
