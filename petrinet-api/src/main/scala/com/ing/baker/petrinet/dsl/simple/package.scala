package com.ing.baker.petrinet.dsl

import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime._

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object simple {

  /**
   * Type alias for the node type of the scalax.collection.Graph backing the petri net.
   */
  type Node = Either[Place[_], Transition[_]]

  /**
   * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
   */
  type Arc = WLDiEdge[Node]

  type Place[C] = Int

  type Transition[O] = Int

  type MarkingLike[T] = T ⇒ SimpleMarking

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.toLong)
  implicit def transitionIdentifier(t: Transition[_]): Id = Id(t.toLong)

  type SimpleMarking = MultiSet[Int]

  case class TransitionAdjacency(in: SimpleMarking, out: SimpleMarking)

  implicit def toSimpleMarking1(p: Int): SimpleMarking = Map(p -> 1)
  implicit def toSimpleMarking2(p: (Int, Int)): SimpleMarking = Map(p._1 -> 1, p._2 -> 1)
  implicit def toSimpleMarking3(p: (Int, Int, Int)): SimpleMarking = Map(p._1 -> 1, p._2 -> 1, p._3 -> 1)
  implicit def toSimpleMarkingSeq(p: Seq[Int]): SimpleMarking = p.map(_ -> 1).toMap

  implicit class ADJ[In: MarkingLike](in: In) {
    def ~|~>[Out: MarkingLike](out: Out): TransitionAdjacency = TransitionAdjacency(implicitly[MarkingLike[In]].apply(in), implicitly[MarkingLike[Out]].apply(out))
  }

  def |~>[Out: MarkingLike](out: Out): TransitionAdjacency = TransitionAdjacency(Map.empty, implicitly[MarkingLike[Out]].apply(out))

  val runtime = new PetriNetRuntime[Place, Transition, Unit, Unit] {
    override val taskProvider: TransitionTaskProvider[Unit, Place, Transition] = new TransitionTaskProvider[Unit, Place, Transition] {
      override def apply[Input, E](petriNet: PetriNet[Place[_], Transition[_]], t: Transition[Input]): TransitionTask[Place, Input, E, Unit] =
        (marking, state, input) ⇒ ???
    }
  }

  def seq(n: Int, start: Int = 1): Seq[TransitionAdjacency] = (start to (start + n)).map(i ⇒ i ~|~> (i + 1))

  def branch(branchFactor: Int, start: Int = 1): TransitionAdjacency = start ~|~> ((start + 1) to (start + branchFactor))

  def tree(branchFactor: Int, depth: Int, start: Int = 1): Seq[TransitionAdjacency] = {

    if (depth == 0)
      Seq.empty
    else {
      val b = branch(branchFactor, start)
      b.out.keys.foldLeft(Seq(b)) {
        case (accTree, n) ⇒
          val subTreeRoot = accTree.flatMap(a ⇒ a.in.keys ++ a.out.keys).max + 1
          val subTree = tree(branchFactor, depth - 1, subTreeRoot)
          val connection = n ~|~> subTreeRoot
          accTree ++ subTree :+ connection
      }
    }
  }

  def createPetriNet(adjacencies: TransitionAdjacency*): PetriNet[Place[_], Transition[_]] = {
    val params: Seq[Arc] = adjacencies.toSeq.zipWithIndex.flatMap {
      case (a, t) ⇒
        a.in.map { case (p, weight) ⇒ WLDiEdge[Node, String](Left(p), Right(t + 1))(weight, "") }.toSeq ++
          a.out.map { case (p, weight) ⇒ WLDiEdge[Node, String](Right(t + 1), Left(p))(weight, "") }.toSeq
    }

    new ScalaGraphPetriNet(Graph(params: _*))
  }
}
