package com.ing.baker.il.dot

import io.kagera.api.MultiSet

import scalax.collection.Graph
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot._
import scalax.collection.io.dot.implicits._

object PetriNetDot {

  def labelFn[P, T]: Either[P, T] ⇒ String = node ⇒ node match {
    case Left(p)  ⇒ s"p$p"
    case Right(t) ⇒ s"t$t"
  }

  def petriNetTheme[P, T]: GraphTheme[Either[P, T], WLDiEdge] = new GraphTheme[Either[P, T], WLDiEdge] {

    override def nodeLabelFn = labelFn

    override def nodeDotAttrFn = node ⇒ node match {
      case Left(nodeA)  ⇒ List(DotAttr("shape", "circle"))
      case Right(nodeB) ⇒ List(DotAttr("shape", "square"))
    }
  }

  def markedPetriNetTheme[P, T](marking: MultiSet[P]): GraphTheme[Either[P, T], WLDiEdge] =
    new GraphTheme[Either[P, T], WLDiEdge] {

      override def nodeLabelFn = labelFn
      override def nodeDotAttrFn = node ⇒ node match {
        case Left(nodeA) ⇒
          marking.get(nodeA) match {
            case Some(n) if n > 0 ⇒ List(DotAttr("shape", "doublecircle"), DotAttr("color", "darkorange"), DotAttr("style", "filled"), DotAttr("fillcolor", "darkorange"), DotAttr("penwidth", 2))
            case _                ⇒ List(DotAttr("shape", "circle"), DotAttr("color", "darkorange"), DotAttr("penwidth", 2))
          }
        case Right(nodeB) ⇒ List(DotAttr("shape", "square"))
      }
    }

  // TODO Generalize this for all types of graphs
  implicit class PetriNetVisualization[P, T](graph: Graph[Either[P, T], WLDiEdge]) {

    def toDot(): String = toDot(petriNetTheme[P, T])

    def toDot(theme: GraphTheme[Either[P, T], WLDiEdge]): String = GraphDot.generateDot(graph, theme)
  }
}
