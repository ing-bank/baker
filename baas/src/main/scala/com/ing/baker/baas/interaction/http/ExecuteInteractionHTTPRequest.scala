package com.ing.baker.baas.interaction.http

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.types.Value

case class ExecuteInteractionHTTPRequest(interaction: InteractionTransition[_], input: Seq[Value])
