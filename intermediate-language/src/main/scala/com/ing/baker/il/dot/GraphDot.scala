package com.ing.baker.il.dot

import scalax.collection.Graph
import scalax.collection.GraphPredef.EdgeLikeIn
import scalax.collection.io.dot._
import scalax.collection.io.dot.implicits._

object GraphDot {

  def generateDot[N, E[X] <: EdgeLikeIn[X]](graph: Graph[N, E], theme: GraphTheme[N, E]) = {
    val myRoot = DotRootGraph(
      directed = graph.isDirected,
      id = None,
      attrStmts = theme.attrStmts,
      attrList = theme.rootAttrs)

    def myNodeTransformer(innerNode: Graph[N, E]#NodeT): Option[(DotGraph, DotNodeStmt)] = {
      Some((myRoot, DotNodeStmt(theme.nodeLabelFn(innerNode.value), theme.nodeDotAttrFn(innerNode.value))))
    }

    def myEdgeTransformer(innerEdge: Graph[N, E]#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {

      // TODO this is not generic enough
      val source = innerEdge.edge.sources.head.value
      val target = innerEdge.edge.targets.head.value

      Some((myRoot, DotEdgeStmt(theme.nodeLabelFn(source), theme.nodeLabelFn(target), List.empty)))
    }

    graph2DotExport(graph).toDot(
      dotRoot = myRoot,
      edgeTransformer = myEdgeTransformer,
      cNodeTransformer = Some(myNodeTransformer))
  }


  // TODO Generalize this for all types of graphs
  implicit class GraphVisualization[N, E[X] <: EdgeLikeIn[X]](graph: Graph[N, E]) {

    def toDot(theme: GraphTheme[N, E]): String = generateDot(graph, theme)
  }
}
