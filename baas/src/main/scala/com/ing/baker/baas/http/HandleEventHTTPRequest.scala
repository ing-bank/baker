package com.ing.baker.baas.http

import com.ing.baker.runtime.core.RuntimeEvent

case class HandleEventHTTPRequest(recipeName: String, requestId: String, runtimeEvent: RuntimeEvent){}
