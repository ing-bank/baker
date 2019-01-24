package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.RuntimeEvent

case class EventsResponse(events: Seq[RuntimeEvent]) extends BaasResponse
