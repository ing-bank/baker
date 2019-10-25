package com.ing.baker.baas.spec

import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.serialization.Encryption

class ScalaDSLBaaSServerClientSpec extends CommonBaaSServerClientSpec(
  (host, as, mat) => BakerClient.build(host, Encryption.NoEncryption)(as, mat)
)

