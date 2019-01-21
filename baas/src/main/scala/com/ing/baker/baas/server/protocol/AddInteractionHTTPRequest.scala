package com.ing.baker.baas.server.protocol

import com.ing.baker.types.Type

case class AddInteractionHTTPRequest(name: String, uri: String, inputTypes: Seq[Type])
