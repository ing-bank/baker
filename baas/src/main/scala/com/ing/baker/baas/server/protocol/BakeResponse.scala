package com.ing.baker.baas.server.protocol

import com.ing.baker.runtime.core.ProcessState

case class BakeResponse(processState: ProcessState) extends BaasResponse
