package com.ing.baker.petrinet.api

import com.ing.baker.petrinet.dsl.simple._
import org.scalatest.{Matchers, WordSpec}

class PetriNetAnalysisSpec extends WordSpec with Matchers {

  "The PetriNetAnalysis class" should {

    "correctly asses the reachability of a very simple petri net A" in {

      val boundedNet = createPetriNet(
        1 ~|~> (2, 3),
        2 ~|~> 4,
        3 ~|~> 5,
        (4, 5) ~|~> 6,
        1 ~|~> 7
      )

      val initialMarking = Map(1 -> 1)

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
