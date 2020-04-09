package com.ing.baker.baas.javadsl

import com.ing.baker.baas.scaladsl.{BakerClient => ScalaRemoteBaker}
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}

object BakerClient {

  def build(hostname: String): JavaBaker =
    new JavaBaker(ScalaRemoteBaker.blocking(hostname))
}
