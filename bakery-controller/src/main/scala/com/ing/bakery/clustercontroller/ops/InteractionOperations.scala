package com.ing.bakery.clustercontroller.ops

import cats.effect.{ContextShift, IO, Timer}
import com.ing.bakery.clustercontroller.ResourceOperations
import skuber.LabelSelector.IsEqualRequirement
import skuber.api.client.KubernetesClient
import skuber.ext.{Deployment, ReplicaSetList}
import skuber.{Container, LabelSelector, ObjectMeta, Pod, PodList, Protocol, Service, Volume}
import skuber.json.ext.format._
import skuber.json.format._

import scala.concurrent.Future

object InteractionOperations {

  def ops(implicit cs: ContextShift[IO], timer: Timer[IO]): (InteractionResource, KubernetesClient) => ResourceOperations[InteractionResource] = { (resource, k8s) =>
    new ResourceOperations[InteractionResource] {

      private def io[A](ref: => Future[A])(implicit cs: ContextShift[IO]): IO[A] =
        IO.fromFuture(IO(ref))

      def create: IO[Unit] = {
        val dplmnt = deployment(resource)
        for {
          _ <- io(k8s.create(dplmnt))
          _ <- Utils.eventually {
            io(k8s.get[Deployment](dplmnt.metadata.name)).map { dp =>
              println()
              println(s"Checking the available pods for deployment '${dp.metadata.name}, available replicas: ${dp.status.map(_.availableReplicas)}")
              println()
              assert(dp.status.forall(_.availableReplicas >= 1))
            }
          }
          _ <- io(k8s.create(service(resource)))
        } yield ()
      }

      def terminate: IO[Unit] = {
        val (key, value) = interactionLabel(resource)
        for {
          _ <- io(k8s.delete[Service](service(resource).name))
          _ <- io(k8s.delete[Deployment](deployment(resource).name))
          _ <- io(k8s.deleteAllSelected[ReplicaSetList](LabelSelector(IsEqualRequirement(key, value))))
          _ <- io(k8s.deleteAllSelected[PodList](LabelSelector(IsEqualRequirement(key, value))))
        } yield ()
      }

      def upgrade: IO[Unit] =
        for {
          _ <- io(k8s.update[skuber.ext.Deployment](deployment(resource)))
        } yield ()
    }
  }

  def interactionLabel(interaction: InteractionResource): (String, String) = "interaction" -> interaction.name

  def serviceName(name: String): String = name + "-interaction-service"

  val baasComponentLabel: (String, String) = "baas-component" -> "remote-interaction"

  val httpAPIPort: Container.Port = Container.Port(
    name = "http-api",
    containerPort = 8080,
    protocol = Protocol.TCP
  )

  def deployment(interaction: InteractionResource): Deployment = {

    val name: String = interaction.name
    val image: String = interaction.spec.image
    val replicas: Int = interaction.spec.replicas

    val healthProbe = skuber.Probe(
      action = skuber.HTTPGetAction(
        port = Right(httpAPIPort.name),
        path = "/api/v3/health"
      ),
      initialDelaySeconds = 15,
      timeoutSeconds = 10
    )

    val interactionContainer = Container(
      name = name,
      image = image)
      .exposePort(httpAPIPort)
      .withReadinessProbe(healthProbe)
      .withLivenessProbe(healthProbe)
      .copy(env = interaction.spec.env)
      .setEnvVar("JAVA_TOOL_OPTIONS", "-XX:+UseContainerSupport -XX:MaxRAMPercentage=85.0")
      // todo parametrise?
      .requestMemory("256M")
      .requestCPU("200m")

    val interactionContainerWithMounts0 =
      interaction.spec.configMapMounts.foldLeft(interactionContainer) { (container, configMount) =>
        container.mount(configMount.name, configMount.mountPath, readOnly = true)
      }

    val interactionContainerWithMounts1 =
      interaction.spec.secretMounts.foldLeft(interactionContainerWithMounts0) { (container, configMount) =>
        container.mount(configMount.name, configMount.mountPath, readOnly = true)
      }

    val volumesConfigMaps =
      interaction.spec.configMapMounts.map { configMount =>
        Volume(configMount.name, Volume.ConfigMapVolumeSource(configMount.name))
      }

    val volumesSecrets =
      interaction.spec.secretMounts.map { configMount =>
        Volume(configMount.name, Volume.Secret(configMount.name))
      }

    val podSpec = Pod.Spec(
      containers = List(interactionContainerWithMounts1),
      volumes = volumesConfigMaps ++ volumesSecrets,
    )

    val podTemplate = Pod.Template.Spec
      .named(name)
      .withPodSpec(podSpec)
      .addLabel(interactionLabel(interaction))

    new Deployment(metadata = ObjectMeta(
      name = name,
      labels = Map(interactionLabel(interaction))
    ))
      .withReplicas(replicas)
      .withTemplate(podTemplate)
  }

  def service(interaction: InteractionResource): Service = {
    Service(serviceName(interaction.name))
      .addLabel(baasComponentLabel)
      .withSelector(interactionLabel(interaction))
      .setPort(Service.Port(
        name = httpAPIPort.name,
        port = httpAPIPort.containerPort
      ))
  }
}
