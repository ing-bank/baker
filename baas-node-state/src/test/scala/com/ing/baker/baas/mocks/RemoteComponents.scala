package com.ing.baker.baas.mocks

import cats.effect.IO

class RemoteComponents(kubeApiServer: KubeApiServer, remoteInteraction: RemoteInteraction, remoteEventListener: RemoteEventListener) {

  def registerToTheCluster: IO[Unit] =
    for {
      _ <- remoteInteraction.publishesItsInterface
      _ <- remoteEventListener.listensToEvents
      _ <- kubeApiServer.registersRemoteComponents
    } yield ()
}
