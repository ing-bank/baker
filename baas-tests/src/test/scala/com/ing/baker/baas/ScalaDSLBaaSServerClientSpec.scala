package com.ing.baker.baas.scaladsl

import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.baas.common.CommonBaaSServerClientSpec

class ScalaDSLBaaSServerClientSpec extends CommonBaaSServerClientSpec(
  (host, as, mat) => Baker.remote(host, Encryption.NoEncryption)(as, mat)
)

