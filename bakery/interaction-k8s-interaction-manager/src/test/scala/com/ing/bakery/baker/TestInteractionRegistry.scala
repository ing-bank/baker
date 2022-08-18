package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.InteractionManager
import com.ing.bakery.baker.mocks.{KubeApiServer, RemoteInteraction}
import com.ing.bakery.components.{BaseInteractionRegistry, LocalhostInteractions}
import com.ing.bakery.interaction.BaseRemoteInteractionClient
import com.typesafe.config.{Config, ConfigValueFactory}
import org.http4s.Headers
import org.http4s.client.Client
import org.mockserver.integration.ClientAndServer

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

class TestInteractionRegistry(c: Config, system: ActorSystem) extends BaseInteractionRegistry(c, system) {

  import TestInteractionRegistry._

  override protected def interactionManagersResource(client: Client[IO]): Resource[IO, List[InteractionManager[IO]]] = {
    val config = c.withValue("baker.interactions.localhost.port", ConfigValueFactory.fromAnyRef(mockServerLocalhost.getLocalPort))
    for {
      localhost <- new LocalhostInteractions(config, system,
        new BaseRemoteInteractionClient(client, Headers.empty)).resource
      kubernetes <- new KubernetesInteractions(
        config, system, new BaseRemoteInteractionClient(client, Headers.empty),
        Some(skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServerKubernetes.getLocalPort))(system))
      ).resource
    } yield List(kubernetes, localhost)
  }

}
