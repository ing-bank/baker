package com.ing.baker.petrinet.api

import com.ing.baker.il.petrinet.{IntermediateTransition, Place, Transition}
import com.ing.baker.il.petrinet.Place.IngredientPlace
import com.ing.baker.petrinet.api.DSL._
import org.scalatest.matchers.should.Matchers
import org.scalatest.wordspec.AnyWordSpec
import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

object DSL {
  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place, Transition]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  type MarkingLike[T] = T => SimpleMarking

  type SimpleMarking = MultiSet[Place]

  case class TransitionAdjacency(in: SimpleMarking, out: SimpleMarking)

  implicit def toPlace(p:Int): Place = Place(p.toString, IngredientPlace)
  implicit def toPlace(m: (Int, Int)): (Place, Int) = m match { case (k,v) => toPlace(k) -> v }
  implicit def toTransition(p:Int): Transition = new IntermediateTransition(p.toString)
  implicit def toSimpleMarking1(p: Place): SimpleMarking = Map(p -> 1)
  implicit def toSimpleMarking1(p: Int): SimpleMarking = Map(toPlace(p) -> 1)
  implicit def toSimpleMarking2(p: (Int, Int)): SimpleMarking = Map(toPlace(p._1) -> 1, toPlace(p._2) -> 1)
  implicit def toSimpleMarking3(p: (Int, Int, Int)): SimpleMarking = Map(toPlace(p._1) -> 1, toPlace(p._2) -> 1, toPlace(p._3) -> 1)
  implicit def toSimpleMarkingSeq(p: Seq[Int]): SimpleMarking = p.map(toPlace(_) -> 1).toMap
  implicit class ADJ[In: MarkingLike](in: In) {
    def ~|~>[Out: MarkingLike](out: Out): TransitionAdjacency = TransitionAdjacency(implicitly[MarkingLike[In]].apply(in), implicitly[MarkingLike[Out]].apply(out))
  }

  def |~>[Out: MarkingLike](out: Out): TransitionAdjacency = TransitionAdjacency(Map.empty, implicitly[MarkingLike[Out]].apply(out))

  def seq(n: Int, start: Int = 1): Seq[TransitionAdjacency] = (start to (start + n)).map(i => i ~|~> (i + 1))

  def branch(branchFactor: Int, start: Int = 1): TransitionAdjacency = start ~|~> ((start + 1) to (start + branchFactor))

  def tree(branchFactor: Int, depth: Int, start: Int = 1): Seq[TransitionAdjacency] = {

    if (depth == 0)
      Seq.empty
    else {
      val b = branch(branchFactor, start)
      b.out.keys.foldLeft(Seq(b)) {
        case (accTree, n) =>
          val subTreeRoot = accTree.flatMap(a => a.in.keys ++ a.out.keys).map(_.getId).max.toInt + 1
          val subTree = tree(branchFactor, depth - 1, subTreeRoot)
          val connection = n ~|~> subTreeRoot
          accTree ++ subTree :+ connection
      }
    }
  }

  def createPetriNet(adjacencies: TransitionAdjacency*): PetriNet = {
    val params: Seq[Arc] = adjacencies.toSeq.zipWithIndex.flatMap {
      case (a: TransitionAdjacency, t) =>
        a.in.map { case (p, weight) => WLDiEdge[Node, String](Left(p), Right(toTransition(t + 1)))(weight, "") }.toSeq ++
          a.out.map { case (p, weight) => WLDiEdge[Node, String](Right(toTransition(t + 1)), Left(p))(weight, "") }.toSeq
    }

    new PetriNet(Graph(params: _*))
  }
}

class PetriNetAnalysisSpec extends AnyWordSpec with Matchers {

  "The PetriNetAnalysis class" should {

    "correctly asses the reachability of a very simple petri net A" in {

      val boundedNet = createPetriNet(
        1 ~|~> (2, 3),
        2 ~|~> 4,
        3 ~|~> 5,
        (4, 5) ~|~> 6,
        1 ~|~> 7
      )

      val initialMarking: SimpleMarking = Map(1 -> 1)

      val tree = PetriNetAnalysis.calculateCoverabilityTree(boundedNet, initialMarking)

      tree.isCoverable(Map(2 -> 1, 3 -> 1, 4 -> 1)) shouldBe false
      tree.isCoverable(Map(4 -> 1)) shouldBe true
      tree.isCoverable(Map(5 -> 1)) shouldBe true
      tree.isCoverable(Map(6 -> 1)) shouldBe true
      tree.isCoverable(Map(6 -> 1, 1 -> 1)) shouldBe false
    }

    "be able to create the coverability tree" in {

      val unboundedNet = createPetriNet(
        (1) ~|~> (1, 2)
      )

      val tree = PetriNetAnalysis.calculateCoverabilityTree(unboundedNet, Map(1 -> 1))

      tree.isCoverable(Map(1 -> 1, 2 -> 10)) shouldBe true
    }
  }
}
