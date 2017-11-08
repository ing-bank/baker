package com.ing.baker.baas.http

import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.types.Value

case class AddInteractionHTTPRequest(name: String, hostname: String, port: Integer){}
