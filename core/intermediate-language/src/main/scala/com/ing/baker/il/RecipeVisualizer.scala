package com.ing.baker.il

import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet._
import com.ing.baker.petrinet.api._
import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import scalax.collection.Graph
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot.implicits._
import scalax.collection.io.dot.{DotAttr, _}

import scala.language.higherKinds

object RecipeVisualizer {

  @transient
  lazy val logger: Logger = Logger(LoggerFactory.getLogger(getClass.getName))

  type RecipePetriNetGraph = Graph[Either[Place, Transition], WLDiEdge]

  implicit class RecipePetriNetGraphFns(graph: RecipePetriNetGraph) {

    def compactNode(node: RecipePetriNetGraph#NodeT): RecipePetriNetGraph = {

      // create direct edges from all incoming to outgoing nodes
      val newEdges = node.incomingNodes.flatMap {incomingNode =>
        node.outgoingNodes.map(n => WLDiEdge[Node, String](incomingNode, n)(0, ""))
      }

      // remove the node, removes all it's incoming and outgoing edges and add the new direct edges
      graph - node -- node.incoming -- node.outgoing ++ newEdges
    }

    def compactAllNodes(fn: RecipePetriNetGraph#NodeT => Boolean): RecipePetriNetGraph = {
      val nodes = graph.nodes.filter(node => fn(node))
      val newEdges = nodes.flatMap(node => node.incomingNodes.flatMap { incomingNode =>
        node.outgoingNodes.map(n => WLDiEdge[Node, String](incomingNode, n)(0, ""))
      })
      graph -- nodes ++ newEdges
    }

    def compactSubRecipes: RecipePetriNetGraph = {
      graph.nodes
        .filter { node =>
          node.value match {
            case Right(transition: Transition) => transition.label.startsWith(subRecipePrefix)
            case _ => false
          }
        }
        .groupBy { node =>
          node.value match {
            case Left(place) => place.label.split('$')(2)
            case Right(transition: Transition) => transition.label.split('$')(2)
          }
        }
        .foldLeft(graph) { case (acc, (name, subRecipeNodes)) =>

          def hasOnlySubInteractionOutNeighbors(nodes: Set[graph.NodeT]): Boolean = {
            nodes
              .filter(_.value match {
                case Right(_: InteractionTransition) => true
                case _ => false
              })
              .diff(subRecipeNodes)
              .isEmpty
          }

          val firstLayer = subRecipeNodes
            .flatMap { n => n.outNeighbors }
            .filter { e =>
              e.value match {
                case Right(event: EventTransition) => !event.isSensoryEvent
                case _ => false
              }
            }
          val selfRefNodes = firstLayer
            .flatMap {
              node => {
                val secondLayer = node.outNeighbors.filter(_.value match {
                  case Left(Place(_, IngredientPlace)) => true
                  case Left(Place(_, EventOrPreconditionPlace)) => true
                  case _ => false
                })
                val eventNodes =
                  if (hasOnlySubInteractionOutNeighbors(node.outNeighbors ++ secondLayer.flatMap(_.outNeighbors))) Set(node)
                  else Set.empty
                eventNodes ++ secondLayer.filter(i => hasOnlySubInteractionOutNeighbors(i.outNeighbors))
              }
            }

          val newNode = Left(Place(name, Place.SubRecipePlace))
          val inEdges = subRecipeNodes.flatMap { node => node.inNeighbors.diff(selfRefNodes).map(n => WLDiEdge[Node, String](n, newNode)(0, "")) }
          val outEdges = subRecipeNodes.flatMap { node => node.outNeighbors.diff(selfRefNodes).map(n => WLDiEdge[Node, String](newNode, n)(0, "")) }
          acc -- selfRefNodes -- subRecipeNodes ++ inEdges ++ outEdges + newNode
        }
    }
  }

  /**
   * Returns the label for a node.
   */
  private def nodeLabelFn: Either[Place, Transition] => String = {
    case Left(Place(label, EmptyEventIngredientPlace)) => s"empty:${label}"
    case Left(place) => place.label
    case Right(transition: MultiFacilitatorTransition) => s"multi:${transition.label}"
    case Right(transition) => transition.label
  }

  /**
   * Returns the style attributes for a node.
   */
  private def nodeDotAttrFn(style: RecipeVisualStyle): (RecipePetriNetGraph#NodeT, Set[String], Set[String]) => List[DotAttr] =
    (node: RecipePetriNetGraph#NodeT, eventNames: Set[String], ingredientNames: Set[String]) =>
      node.value match {
        case Left(Place(_, SubRecipePlace)) => style.subRecipe
        case Left(Place(_, InteractionEventOutputPlace)) => style.choiceAttributes
        case Left(Place(_, EventOrPreconditionPlace)) => style.preconditionORAttributes
        case Left(Place(_, EmptyEventIngredientPlace)) => style.emptyEventAttributes
        case Left(_: Place) if node.incomingTransitions.isEmpty => style.missingIngredientAttributes
        case Left(Place(label, _)) if ingredientNames contains label => style.providedIngredientAttributes
        case Left(_) => style.ingredientAttributes
        case Right(t: InteractionTransition) if eventNames.intersect(t.eventsToFire.map(_.name).toSet).nonEmpty => style.firedInteractionAttributes
        case Right(_: InteractionTransition) => style.interactionAttributes
        case Right(transition: Transition) if eventNames.contains(transition.label) => style.eventFiredAttributes
        case Right(_: MultiFacilitatorTransition) => style.choiceAttributes
        case Right(_: MissingEventTransition) => style.eventMissingAttributes
        case Right(EventTransition(_, true, _)) => style.sensoryEventAttributes
        case Right(_) => style.eventAttributes
      }

  private def generateDot(graph: RecipePetriNetGraph, style: RecipeVisualStyle, filter: String => Boolean, eventNames: Set[String], ingredientNames: Set[String], subRecipe: Boolean): String = {

    val myRoot = DotRootGraph(directed = graph.isDirected,
      id = None,
      attrStmts = style.commonNodeAttributes,
      attrList = style.rootAttributes)

    def recipeNodeTransformer(innerNode: RecipePetriNetGraph#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(nodeLabelFn(innerNode.value), nodeDotAttrFn(style)(innerNode, eventNames, ingredientNames))))
    }

    def recipeEdgeTransformer(innerEdge: RecipePetriNetGraph#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {

      val source = innerEdge.edge.source
      val target = innerEdge.edge.target

      Some((myRoot, DotEdgeStmt(nodeLabelFn(source.value), nodeLabelFn(target.value), List.empty)))
    }

    // specifies which places to compact (remove)
    val placesToCompact = (node: RecipePetriNetGraph#NodeT) => node.value match {
      case Left(Place(_, IngredientPlace)) => false
      case Left(Place(_, EmptyEventIngredientPlace)) => false
      case Left(Place(_, EventOrPreconditionPlace)) => false
      case Left(Place(_, _)) => true
      case _ => false
    }

    val sievesInteractionToCompact = (node: RecipePetriNetGraph#NodeT) => node.value match {
      case Right(transition: Transition) => transition.label.startsWith(sieveInteractionPrefix)
      case _ => false
    }
    val sievesEventsToCompact = (node: RecipePetriNetGraph#NodeT) => node.value match {
      case Right(transition: Transition) => transition.label.startsWith(sieveEventPrefix)
      case _ => false
    }

    // specifies which transitions to compact (remove)
    val transitionsToCompact = (node: RecipePetriNetGraph#NodeT) => node.value match {
      case Right(transition: Transition) =>
        transition.isInstanceOf[IntermediateTransition] ||
          transition.isInstanceOf[MultiFacilitatorTransition] ||
          transition.label.startsWith(checkpointEventInteractionPrefix)

      case _ => false
    }

    // compacts all nodes that are not of interest to the recipe
    val compactedGraph =
      if (subRecipe) {
        graph
          .compactAllNodes(placesToCompact)
          .compactAllNodes(transitionsToCompact)
          .compactSubRecipes
          .compactAllNodes(sievesInteractionToCompact)
          .compactAllNodes(sievesEventsToCompact)
      } else {
        graph
          .compactAllNodes(placesToCompact)
          .compactAllNodes(transitionsToCompact)
          .compactAllNodes(sievesInteractionToCompact)
          .compactAllNodes(sievesEventsToCompact)
      }
    // filters out all the nodes that match the predicate function
    val filteredGraph = compactedGraph -- compactedGraph.nodes.filter(n => !filter(n.toString))

    // creates the .dot representation
    graph2DotExport(filteredGraph).toDot(dotRoot = myRoot,
      edgeTransformer = recipeEdgeTransformer,
      cNodeTransformer = Some(recipeNodeTransformer))
  }

  def visualizeRecipe(recipe: CompiledRecipe,
                      style: RecipeVisualStyle,
                      filter: String => Boolean = _ => true,
                      eventNames: Set[String] = Set.empty,
                      ingredientNames: Set[String] = Set.empty): String =
    generateDot(recipe.petriNet.innerGraph, style, filter, eventNames, ingredientNames, false)

  def visualizeSubRecipe(recipe: CompiledRecipe,
                         style: RecipeVisualStyle,
                         filter: String => Boolean = _ => true,
                         eventNames: Set[String] = Set.empty,
                         ingredientNames: Set[String] = Set.empty): String =
    generateDot(recipe.petriNet.innerGraph, style, filter, eventNames, ingredientNames, true)

  def visualizePetriNet(graph: PetriNetGraph, placeLabelFn: Place => String = (p: Place) => p.toString, transitionLabelFn: Transition => String = (t: Transition) => t.toString): String = {

    val nodeLabelFn: Either[Place, Transition] => String = {
      case Left(p) => placeLabelFn(p)
      case Right(t) => transitionLabelFn(t)
    }

    val nodeDotAttrFn: Either[Place, Transition] => List[DotAttr] = {
      case Left(_) => List(DotAttr("shape", "circle"))
      case Right(_) => List(DotAttr("shape", "square"))
    }

    val myRoot = DotRootGraph(
      directed = graph.isDirected,
      id = None,
      attrStmts = List.empty,
      attrList = List.empty)

    def myNodeTransformer(innerNode: PetriNetGraph#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(nodeLabelFn(innerNode.value), nodeDotAttrFn(innerNode.value))))
    }

    def myEdgeTransformer(innerEdge: PetriNetGraph#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {

      val source = innerEdge.edge.sources.head.value
      val target = innerEdge.edge.targets.head.value

      Some((myRoot, DotEdgeStmt(nodeLabelFn(source), nodeLabelFn(target), List.empty)))
    }

    graph2DotExport(graph).toDot(
      dotRoot = myRoot,
      edgeTransformer = myEdgeTransformer,
      cNodeTransformer = Some(myNodeTransformer))
  }
}
