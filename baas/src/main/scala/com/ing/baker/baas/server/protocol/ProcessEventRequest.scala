package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.RuntimeEvent

case class ProcessEventRequest(event: RuntimeEvent) extends BaasRequest
