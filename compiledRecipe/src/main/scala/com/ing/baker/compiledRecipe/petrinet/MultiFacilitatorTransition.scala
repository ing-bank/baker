package com.ing.baker.compiledRecipe.petrinet

import com.ing.baker.core.ProcessState

case class MultiFacilitatorTransition(override val id: Long, override val label: String) extends Transition[Unit, Unit, ProcessState]
