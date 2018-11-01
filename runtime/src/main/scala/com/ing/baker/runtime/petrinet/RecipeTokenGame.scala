package com.ing.baker.runtime.petrinet

import com.ing.baker.il.petrinet.{Edge, Place, Transition}
import com.ing.baker.petrinet.api._
import com.ing.baker.petrinet.runtime.TokenGame

class RecipeTokenGame extends TokenGame[Place, Transition] {
  override def consumableTokens(petriNet: PetriNet[Place, Transition])(marking: Marking[Place], p: Place, t: Transition): MultiSet[Any] = {
    val edge = petriNet.findPTEdge(p, t).map(_.asInstanceOf[Edge]).get

    marking.get(p) match {
      case None         ⇒ MultiSet.empty
      case Some(tokens) ⇒ tokens.filter { case (e, count) ⇒ edge.isAllowed(e) }
    }
  }
}
