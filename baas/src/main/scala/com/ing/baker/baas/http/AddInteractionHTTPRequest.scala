package com.ing.baker.baas.http

import com.ing.baker.types.Type

case class AddInteractionHTTPRequest(name: String, uri: String, inputTypes: Seq[Type])
