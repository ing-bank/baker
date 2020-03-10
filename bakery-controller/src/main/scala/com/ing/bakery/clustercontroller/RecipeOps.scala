package com.ing.bakery.clustercontroller

import cats.data.Kleisli
import cats.effect.IO
import skuber.api.client.KubernetesClient

trait RecipeOps[F[_]] {

  def pingBakeryClusterVersion: F[Option[String]]

  def createBakeryCluster: F[Unit]

  def terminateBakeryCluster: F[Unit]

  def upgradeBakeryCluster: F[Unit]
}

object RecipeOps {

  type RecipeK8sOperation[A] = Kleisli[IO, (RecipeResource, KubernetesClient), A]

  def context[A](f: (RecipeResource, KubernetesClient) => IO[A]): RecipeK8sOperation[A] =
    Kleisli.apply[IO, (RecipeResource, KubernetesClient), A] {
      case (recipe, client) => f(recipe, client)
    }

  object k8s extends RecipeOps[RecipeK8sOperation] {

    def pingBakeryClusterVersion: RecipeK8sOperation[Option[String]] =
      context { (resource, k8s) =>
        IO.unit
      }

    def createBakeryCluster: RecipeK8sOperation[Unit] =
      context { (resource, k8s) =>
        IO.unit
      }

    def terminateBakeryCluster: RecipeK8sOperation[Unit] =
      context { (resource, k8s) =>
        IO.unit
      }

    def upgradeBakeryCluster: RecipeK8sOperation[Unit] =
      context { (resource, k8s) =>
        IO.unit
      }
  }
}
