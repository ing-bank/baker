package com.ing.baker.baas.interaction.server.protocol

import com.ing.baker.baas.server.protocol.BaasRequest
import com.ing.baker.runtime.core.RuntimeEvent

case class ExecuteInteractionHTTPResponse(runtimeEventOptional: Option[RuntimeEvent]) extends BaasRequest
