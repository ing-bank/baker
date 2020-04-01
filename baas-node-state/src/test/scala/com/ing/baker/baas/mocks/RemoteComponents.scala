package com.ing.baker.baas.mocks

import cats.effect.IO

class RemoteComponents(kubeApiServer: KubeApiServer, remoteInteraction: RemoteInteraction) {

  def registerToTheCluster: IO[Unit] =
    for {
      _ <- remoteInteraction.publishesItsInterface
      _ <- kubeApiServer.registersRemoteComponents
    } yield ()
}
