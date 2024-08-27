package com.ing.baker.runtime.akka.actor.process_instance.dsl

import com.ing.baker.il.petrinet.Place
import com.ing.baker.il.petrinet.Place.IngredientPlace
import com.ing.baker.petrinet.api._

object TestUtils {
  def place(id: Long): Place = new Place(s"p$id", IngredientPlace)
  implicit class PlaceMethods(val place: Place) {

    //  def apply(tokens: Any*): (Place, MultiSet[Any]) = (this, MultiSet.copyOff(tokens))

    def markWithN(n: Int): Marking[Place] = Map[Place, MultiSet[Any]](place -> Map[Any, Int](Tuple2(null, n)))
  }

  implicit class TransitionMethods(val transition: com.ing.baker.il.petrinet.Transition) {
    val exceptionStrategy =
      transition match {
        case st: StateTransition[_, _] => st.exceptionStrategy
      }
    val isAutomated =
      transition match {
        case st: StateTransition[_, _] => st.isAutomated
      }
  }
}

