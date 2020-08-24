package com.ing.baker.baas.common

import java.security.SecureRandom

import javax.net.ssl.SSLContext

case class TLSConfig(keyManagementKeystore: KeystoreConfig, trustManagementKeystore: KeystoreConfig) {

  def loadSSLContext: SSLContext = {
    val sslContext: SSLContext = SSLContext.getInstance("TLS")
    sslContext.init(keyManagementKeystore.loadAsKeyManager.getKeyManagers, trustManagementKeystore.loadAsTrustManager.getTrustManagers, new SecureRandom)
    sslContext
  }
}
