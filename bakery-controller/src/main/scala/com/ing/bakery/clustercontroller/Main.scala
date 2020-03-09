package com.ing.bakery.clustercontroller

import akka.actor.ActorSystem
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp}
import cats.syntax.functor._
import skuber.api.client.KubernetesClient

object Main extends IOApp {

  override def run(args: List[String]): IO[ExitCode] = {

    implicit val system: ActorSystem =
      ActorSystem("BaaSStateNodeSystem")
    implicit val materializer: Materializer =
      ActorMaterializer()
    val k8s: KubernetesClient = skuber.k8sInit

    RecipeController.resource(k8s)
      .use(_ => IO.never).as(ExitCode.Success)
  }
}
