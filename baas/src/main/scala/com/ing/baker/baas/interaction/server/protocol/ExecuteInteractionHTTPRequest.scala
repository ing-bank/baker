package com.ing.baker.baas.interaction.server.protocol

import com.ing.baker.baas.server.protocol.BaasRequest
import com.ing.baker.types.Value

case class ExecuteInteractionHTTPRequest(input: Seq[Value]) extends BaasRequest
