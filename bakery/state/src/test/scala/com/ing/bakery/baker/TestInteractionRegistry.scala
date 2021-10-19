package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.InteractionManager
import com.ing.bakery.mocks.{KubeApiServer, RemoteInteraction}
import com.typesafe.config.Config
import org.http4s.client.Client
import org.mockserver.integration.ClientAndServer
import skuber.api.client.KubernetesClient

object TestInteractionRegistry {
  var mockServerKubernetes: ClientAndServer = _
  var mockServerLocalhost: ClientAndServer = _
  var remoteInteractionKubernetes: RemoteInteraction = _
  var remoteInteractionLocalhost: RemoteInteraction = _
  var kubeApiServer: KubeApiServer = _

  def apply(mockServerKubernetes: ClientAndServer,
            mockServerLocalhost: ClientAndServer,
            remoteInteractionKubernetes: RemoteInteraction,
            remoteInteractionLocalhost: RemoteInteraction,
            kubeApiServer: KubeApiServer): Unit = {
    this.mockServerKubernetes = mockServerKubernetes
    this.mockServerLocalhost = mockServerLocalhost
    this.remoteInteractionKubernetes = remoteInteractionKubernetes
    this.remoteInteractionLocalhost = remoteInteractionLocalhost
    this.kubeApiServer = kubeApiServer
  }

}

class TestInteractionRegistry(config: Config, system: ActorSystem) extends BaseInteractionRegistry(config, system) {
    import TestInteractionRegistry._
    override protected def interactionManagersResource(client: Client[IO], kubernetesClient: KubernetesClient): Resource[IO, List[InteractionManager[IO]]] =
      for {
        localhost <- new LocalhostInteractions(config, system, client, Some(mockServerLocalhost.getLocalPort)).resource
        kubernetes <- new KubernetesInteractions(
          config, system, client,
          skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServerKubernetes.getLocalPort))(system)
        ).resource
      } yield List(kubernetes, localhost)

}
