package com.ing.baker.baas.http

import com.ing.baker.runtime.core.ProcessState

case class GetStateHTTResponse(processState: ProcessState, visualState: String){}
