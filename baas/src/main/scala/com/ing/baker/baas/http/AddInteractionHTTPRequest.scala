package com.ing.baker.baas.http

import com.ing.baker.types.BType

case class AddInteractionHTTPRequest(name: String, uri: String, inputTypes: Seq[BType])
