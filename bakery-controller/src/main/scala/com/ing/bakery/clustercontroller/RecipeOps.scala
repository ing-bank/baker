package com.ing.bakery.clustercontroller

import cats.syntax.apply._
import cats.data.Kleisli
import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.baas.scaladsl.BakerClient
import org.http4s.Uri
import skuber.{Container, ObjectMeta, Pod, Protocol, Service}
import skuber.api.client.KubernetesClient
import skuber.ext.Deployment
import skuber.json.format._
import skuber.json.ext.format._

import scala.concurrent.duration._

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

  def k8s(implicit cs: ContextShift[IO], timer: Timer[IO]): RecipeOps[RecipeK8sOperation] =
    new RecipeOps[RecipeK8sOperation] {

      val stateNodeLabel: (String, String) = "app" -> "baas-state"

      def recipeLabel(recipeId: String): (String, String) = "recipe" -> recipeId

      def akkaClusterLabel(selector: String): (String, String) = "akka-cluster" -> selector

      val namespace: String = "default"

      def baasStateName(recipeId: String): String = "baas-state-" + recipeId

      def baasStateServiceName(recipeId: String): String = "baas-state-service-" + recipeId

      val baasStateServicePort: Int = 8081

      def eventually[A](f: IO[A]): IO[A] =
        within(30.seconds, 30)(f)

      def within[A](time: FiniteDuration, split: Int)(f: IO[A]): IO[A] = {
        def inner(count: Int, times: FiniteDuration): IO[A] = {
          if (count < 1) f else f.attempt.flatMap {
            case Left(_) => IO.sleep(times) *> inner(count - 1, times)
            case Right(a) => IO(a)
          }
        }

        inner(split, time / split)
      }


      def pingBakeryClusterVersion: RecipeK8sOperation[Option[String]] =
        context { (resource, k8s) =>
          ???
        }

      def createBakeryCluster: RecipeK8sOperation[Unit] =
        context { (resource, k8s) =>
          for {
            compiledRecipe <- resource.decodeRecipe
            recipeId = compiledRecipe.recipeId
            _ <- IO.fromFuture {

              val managementPort = Container.Port(
                name = "management",
                containerPort = 8558,
                protocol = Protocol.TCP
              )

              val stateNodeContainer = Container(
                name = baasStateName(recipeId),
                image = "baas-node-state:" + resource.spec.bakeryVersion
              )
                .exposePort(Container.Port(
                  name = "remoting",
                  containerPort = 2552,
                  protocol = Protocol.TCP
                ))
                .exposePort(managementPort)
                .exposePort(Container.Port(
                  name = "http-api",
                  containerPort = 8080,
                  protocol = Protocol.TCP
                ))
                .withReadinessProbe(skuber.Probe(
                  action = skuber.HTTPGetAction(
                    port = Right(managementPort.name),
                    path = "/health/ready"
                  )
                ))
                .withLivenessProbe(skuber.Probe(
                  action = skuber.HTTPGetAction(
                    port = Right(managementPort.name),
                    path = "/health/alive"
                  )
                ))
                .setEnvVar("STATE_CLUSTER_SELECTOR", recipeId)

              val podTemplate = Pod.Template.Spec
                .named(baasStateName(recipeId))
                .addContainer(stateNodeContainer)
                .addLabel(stateNodeLabel)
                .addLabel(recipeLabel(recipeId))
                .addLabel(akkaClusterLabel(recipeId))

              val deployment = new Deployment(metadata = ObjectMeta(
                name = baasStateName(recipeId),
                labels = Map(stateNodeLabel, recipeLabel(recipeId))
              ))
                .withReplicas(resource.spec.replicas)
                .withTemplate(podTemplate)

              IO(k8s.create(deployment))
            }

            service <- IO.fromFuture {
              val service = Service(baasStateServiceName(recipeId))
                .withLoadBalancerType
                .addLabel("baas-component", "state")
                .addLabel("app", "baas-state-service")
                .addLabel(recipeLabel(recipeId))
                .withSelector(stateNodeLabel)
                .setPort(Service.Port(
                  name = "http-api",
                  port = baasStateServicePort,
                  targetPort = Some(Right("http-api"))
                ))
              IO(k8s.create(service))
            }

            _ <- BakerClient.resource(Uri.unsafeFromString(s"http://${service.metadata.name}:$baasStateServicePort"), scala.concurrent.ExecutionContext.global).use { client => // TODO parametrise a pool for connections
              eventually(IO.fromFuture(IO(client.addRecipe(compiledRecipe))))
            }
          } yield ()
        }

      def terminateBakeryCluster: RecipeK8sOperation[Unit] =
        context { (resource, k8s) =>
          for {
            _ <- IO.unit
          } yield ()
        }

      def upgradeBakeryCluster: RecipeK8sOperation[Unit] =
        context { (resource, k8s) =>
          IO.unit
        }
    }
}
