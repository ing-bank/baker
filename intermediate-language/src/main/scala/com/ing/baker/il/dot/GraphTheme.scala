package com.ing.baker.il.dot

import scalax.collection.GraphPredef.EdgeLikeIn
import scalax.collection.io.dot._
import scalax.collection.io.dot.implicits._

trait GraphTheme[N, E[X] <: EdgeLikeIn[X]] {

  def nodeLabelFn: N => String = node => node.toString

  def nodeDotAttrFn: N => List[DotAttr] = node => List(DotAttr("shape", "circle"))

  def attrStmts: scala.Seq[DotAttrStmt] = List.empty

  def rootAttrs: scala.Seq[DotAttr] = List.empty

//  def edgeDotAttrFn: Graph[N, E#EdgeT => List[DotAttr] = edge => List.empty
}
