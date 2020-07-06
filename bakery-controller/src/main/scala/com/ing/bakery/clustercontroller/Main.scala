package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.baas.interaction.BakeryHttp
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, InteractionController, InteractionResource}
import com.typesafe.config.ConfigFactory
import javax.net.ssl.SSLContext
import kamon.Kamon
import org.http4s.client.blaze.BlazeClientBuilder
import skuber.api.client.KubernetesClient
import skuber.json.format.configMapFmt

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()

    val config = ConfigFactory.load()
    val useCrds = config.getBoolean("bakery-controller.use-crds")
    val interactionClientHttpsEnabled = config.getBoolean("baas-component.interaction-client.https-enabled")
    lazy val interactionClientKeystorePath = config.getString("baas-component.interaction-client.https-keystore-path")
    lazy val interactionClientKeystorePassword = config.getString("baas-component.interaction-client.https-keystore-password")
    lazy val interactionClientKeystoreType = config.getString("baas-component.interaction-client.https-keystore-type")

    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem")
    implicit val materializer: Materializer =
      ActorMaterializer()
    val k8s: KubernetesClient =
      skuber.k8sInit
    implicit val connectionPool =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    val tlsConfig: Option[SSLContext] =
      if(interactionClientHttpsEnabled)
        Some(BakeryHttp.loadSSLContext(BakeryHttp.TLSConfig(
          password = interactionClientKeystorePassword,
          keystorePath = interactionClientKeystorePath,
          keystoreType = interactionClientKeystoreType
        )))
      else None

    (for {
      _ <- BakeryControllerService.resource(InetSocketAddress.createUnresolved("0.0.0.0", 8080))
      interactionHttpClient <- BlazeClientBuilder[IO](connectionPool, tlsConfig).resource
      interactions = new InteractionController(interactionHttpClient)
      bakers = new BakerController()
      _ <- if(useCrds) interactions.watch(k8s) else Resource.liftF(IO.unit)
      _ <- interactions.fromConfigMaps(InteractionResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "interactions"))
      _ <- if(useCrds) bakers.watch(k8s) else Resource.liftF(IO.unit)
      _ <- bakers.fromConfigMaps(BakerResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "bakers"))
    } yield ()).use(_ => IO.never).as(ExitCode.Success)
  }
}
