package com.ing.baker.runtime.baas.scaladsl

import akka.http.scaladsl.model.Uri
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi

class ScalaDSLBaaSServerClientSpec extends CommonBaaSServerClientSpec(
  (host, as, mat) => new Baker(Uri(host), Encryption.NoEncryption)(as, mat)
) with ScalaApi

