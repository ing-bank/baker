package com.ing.baker.runtime.core

import com.ing.baker.il.petrinet.{PTEdge, Place, Transition}
import io.kagera.api._
import io.kagera.runtime.TokenGame

class RecipeTokenGame extends TokenGame[Place, Transition] {
  override def consumableTokens(petriNet: PetriNet[Place[_], Transition[_, _]])(marking: Marking[Place], p: Place[_], t: Transition[_, _]): MultiSet[_] = {
    val edge = petriNet.innerGraph.findPTEdge(p, t).map(_.label.asInstanceOf[PTEdge[Any]]).get

    marking.get(p) match {
      case None         ⇒ MultiSet.empty
      case Some(tokens) ⇒ tokens.filter { case (e, count) ⇒ edge.filter(e) }
    }
  }
}
