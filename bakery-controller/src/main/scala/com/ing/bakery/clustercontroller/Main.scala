package com.ing.bakery.clustercontroller

import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp}
import cats.syntax.functor._
import com.ing.bakery.clustercontroller.controllers.{BakerController, BakerResource, InteractionController, InteractionResource}
import org.http4s.client.blaze.BlazeClientBuilder
import skuber.api.client.KubernetesClient
import skuber.json.format.configMapFmt

import scala.concurrent.ExecutionContext

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {

    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem")
    implicit val materializer: Materializer =
      ActorMaterializer()
    val k8s: KubernetesClient =
      skuber.k8sInit
    val connectionPool =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    (for {
      _ <- BakeryControllerService.resource(InetSocketAddress.createUnresolved("0.0.0.0", 8080))
      httpClient <- BlazeClientBuilder[IO](connectionPool).resource
      interactions = new InteractionController(httpClient)
      bakers = new BakerController()
      _ <- interactions.watch(k8s)
      _ <- interactions.fromConfigMaps(InteractionResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "interactions"))
      _ <- bakers.watch(k8s)
      _ <- bakers.fromConfigMaps(BakerResource.fromConfigMap).watch(k8s, label = Some("custom-resource-definition" -> "bakers"))
    } yield ()).use(_ => IO.never).as(ExitCode.Success)
  }
}
