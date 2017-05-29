package com.ing.baker.compiledRecipe.petrinet

import io.kagera.api.{Marking, MultiSet, PetriNet, ReferenceTokenGame}

class RecipeTokenGame extends ReferenceTokenGame[Place, Transition] {
  override def consumableTokens(petriNet: PetriNet[Place[_], Transition[_, _, _]])(marking: Marking[Place], p: Place[_], t: Transition[_, _, _]): MultiSet[_] = ???
}
