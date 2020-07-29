package com.ing.bakery.clustercontroller

import java.io.ByteArrayInputStream

import cats.effect.{ContextShift, IO}
import com.ing.baker.baas.interaction.BakeryHttp
import com.typesafe.config.Config
import javax.net.ssl.SSLContext
import skuber.api.client.KubernetesClient
import skuber.json.format.secretFmt

case class MutualAuthKeystoreConfig(secretName: String, fileName: String, password: String, _type: String) {

  def loadKeystore(k8s: KubernetesClient)(implicit cs: ContextShift[IO]): IO[SSLContext] =
    for {
      keystoreSecret <- IO.fromFuture(IO(k8s.get[skuber.Secret](secretName)))
      fileNotFound = IO.raiseError[SSLContext](new IllegalStateException(s"Did not find keystore '$fileName' on secret $secretName"))
      loadKeystore = (keystore: Array[Byte]) => IO(BakeryHttp.loadSSLContextFromInputStream(new ByteArrayInputStream(keystore), password, _type))
      sslContext <- keystoreSecret.data
        .get(fileName)
        .fold(fileNotFound)(loadKeystore)
    } yield sslContext
}

object MutualAuthKeystoreConfig {

  def from(config: Config, of: String): Option[MutualAuthKeystoreConfig] = {
    val enabled = config.getBoolean("bakery-controller.https-mutual-auth")
    if(enabled)
      Some(MutualAuthKeystoreConfig(
        secretName = config.getString(s"bakery-controller.$of.https-keystore-secret"),
        fileName = config.getString(s"bakery-controller.$of.https-keystore-name"),
        password = config.getString(s"bakery-controller.$of.https-keystore-password"),
        _type = config.getString(s"bakery-controller.$of.https-keystore-type")
      ))
    else None
  }
}

