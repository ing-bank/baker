package com.ing.bakery.common

import java.io.{File, FileInputStream, InputStream}
import java.security.KeyStore

import javax.net.ssl.{KeyManagerFactory, TrustManagerFactory}

/**
  * Use this to configure the SSLContext of the client, you only need to provide the location and password of a keystore.
  *
  * @param password of the keystore
  * @param keystorePath first the client tries to load it relative to the classpath resources and then absolute to the machine.
  * @param keystoreType for example, JKS
  */
case class KeystoreConfig(password: String, keystorePath: String, keystoreType: String) {

  def loadFile: InputStream = {
    // Try resource directory as root first
    val keystoreResource: InputStream = getClass.getClassLoader.getResourceAsStream(keystorePath)
    // Otherwise try absolute path
    val keystore: InputStream =
      if(keystoreResource == null) new FileInputStream(new File(keystorePath))
      else keystoreResource
    require(keystore != null, s"Keystore of type '$keystoreType' not found on path '$keystorePath', tried classpath resources and then absolute path")
    keystoreResource
  }

  def loadAsKeyManager: KeyManagerFactory = {
    val ks: KeyStore = KeyStore.getInstance(keystoreType)
    val passwordArray: Array[Char] = password.toCharArray
    ks.load(loadFile, passwordArray)
    val keyManagerFactory: KeyManagerFactory = KeyManagerFactory.getInstance("SunX509")
    keyManagerFactory.init(ks, passwordArray)
    keyManagerFactory
  }

  def loadAsTrustManager: TrustManagerFactory = {
    val ks: KeyStore = KeyStore.getInstance(keystoreType)
    val passwordArray: Array[Char] = password.toCharArray
    ks.load(loadFile, passwordArray)
    val tmf: TrustManagerFactory = TrustManagerFactory.getInstance("SunX509")
    tmf.init(ks)
    tmf
  }
}

