package com.ing.baker.baas.common

/**
  * Use this to configure the SSLContext of the client, you only need to provide the location and password of a keystore.
  *
  * @param password of the keystore
  * @param keystorePath first the client tries to load it relative to the classpath resources and then absolute to the machine.
  * @param keystoreType for example, JKS
  */
case class TLSConfig(password: String, keystorePath: String, keystoreType: String)

