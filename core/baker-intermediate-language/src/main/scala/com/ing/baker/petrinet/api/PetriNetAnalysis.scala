package com.ing.baker.petrinet.api

import com.ing.baker.il.petrinet.{Place, Transition}

object PetriNetAnalysis {

  // indicates an unbounded token count in a place
  val W: Int = -1

  implicit class WMarkingOps[P](marking: MultiSet[P]) {
    // this checks if marking m 'covers' another
    def >=(other: MultiSet[P]): Boolean = other.forall {
      case (p, `W`) => marking.get(p).contains(W)
      case (p, n) => marking.get(p) match {
        case Some(m) => m >= n || m == W
        case _       => false
      }
    }
  }

  implicit class PetriNetOps(petriNet: PetriNet) {
    def removeTransitions(transitions: Iterable[Transition]): PetriNet = {
      val graph = transitions.foldLeft(petriNet.innerGraph) {
        case (acc, t) => acc.-(Right(t))
      }
      new PetriNet(graph)
    }
  }

  /**
   * A node in the coverability tree
   */
  class Node(
              var marking: MultiSet[Place],
              var isNew: Boolean,
              var children: Map[Transition, Node]) {

    // returns the path to a new node
    def newNode: Option[List[Node]] =
      if (isNew)
        Some(List(this))
      else
        children.values.view.map(_.newNode.map(nodes => this :: nodes)).find(_.isDefined).map(_.get)

    override def toString: String = {
      val markingString = marking.iterator.map { case (p, n) => s"$p -> ${if (n == W) 'W' else n}" }.mkString(",")
      s"marking: $markingString, children: $children"
    }

    def isCoverable(target: MultiSet[Place]): Boolean = {
      if (marking >= target)
        true
      else
        children.values.exists(_.isCoverable(target))
    }

    def maxNrTokens: Int = (marking.values ++ children.values.map(_.maxNrTokens)).max
  }

  def optimize(petrinet: PetriNet, m0: MultiSet[Place]): (PetriNet, MultiSet[Place]) = {

    val unboundedTransitions = unboundedEnabled(petrinet, m0)

    if (unboundedTransitions.isEmpty)
      (petrinet, m0)
    else {
      // remove the cold transitions to simplify things
      val updatedPetriNet = petrinet.removeTransitions(unboundedTransitions)

      val unboundedOut = unboundedTransitions.foldLeft(MultiSet.empty[Place]) {
        case (acc, t) => acc.multisetSum(petrinet.outMarking(t))
      }.map {
        case (p, _) => p -> W
      }

      optimize(updatedPetriNet, m0 ++ unboundedOut)
    }
  }

  def unboundedEnabled(petrinet: PetriNet, m0: MultiSet[Place]): Iterable[Transition] = {

    val coldTransitions = petrinet.transitions.filter(t => petrinet.incomingPlaces(t).isEmpty)
    val unboundedMarking = m0.filter { case (_, n) => n == W }
    val enabled = unboundedMarking.keys.map(petrinet.outgoingTransitions).reduceOption(_ ++ _).getOrElse(Set.empty).
      filter(t => unboundedMarking >= petrinet.inMarking(t))

    coldTransitions ++ enabled
  }

  /**
   * Implements page 47 of http://cpntools.org/_media/book/covgraph.pdf
   */
  def calculateCoverabilityTree(petrinet: PetriNet, m0: MultiSet[Place]): Node = {

    val (pn, initialMarking) = optimize(petrinet, m0)

    val coldTransitions = petrinet.transitions.filter(t => petrinet.incomingPlaces(t).isEmpty)
    val inMarking = pn.transitions.map(t => t -> petrinet.inMarking(t)).toMap
    val outMarking = pn.transitions.map(t => t -> petrinet.outMarking(t)).toMap

    def fire(m0: MultiSet[Place], t: Transition): MultiSet[Place] = {
      // unbounded places stay unchanged
      val (unbounded, bounded) = m0.partition { case (_, n) => n == W }

      bounded
        .multisetDifference(inMarking(t))
        .multisetSum(outMarking(t)) ++ unbounded
    }

    def enabledTransitions(m0: MultiSet[Place]): Iterator[Transition] = {

      val outAdjacent = m0.keys.map(pn.outgoingTransitions).reduceOption(_ ++ _).getOrElse(Set.empty).
        filter(t => m0 >= inMarking(t))

      outAdjacent.iterator
    }

    // 1. Label the initial marking M0 as the root and tag it 'new'
    val root = new Node(initialMarking, true, Map.empty)

    var newNode = root.newNode

    // while 'new' markings exist
    while (newNode.isDefined) {
      newNode.foreach { pathToM =>

        // the new node
        val node = pathToM.last

        // remove the 'new' tag
        node.isNew = false

        val M = node.marking

        // there exists no marking equal to m on the path from root to m
        if (!pathToM.dropRight(1).exists(_.marking == M)) {

          enabledTransitions(M).foreach { t =>

            // i. obtain the marking that results from firing t at M
            val postT: MultiSet[Place] = fire(M, t)

            // ii. if on the path to m there exists a marking that is covered by M1
            val coverableM: Option[MultiSet[Place]] =
              pathToM.map(_.marking).find(M11 => postT >= M11 && postT != M11)

            val M1: MultiSet[Place] = coverableM.map { M11 =>
              postT.map {
                case (p, n) if n > M11.getOrElse(p, 0) => p -> W
                case (p, n)                            => p -> n
              }
            }.getOrElse(postT)

            // iii. introduce M1 as a node
            val newNode: Node = new Node(M1, true, Map.empty)
            node.children += t -> newNode
          }
        }
      }

      newNode = root.newNode
    }

    root
  }
}
