package com.ing.baker.baas.mocks

import scala.concurrent.{ExecutionContext, Future}

class RemoteComponents(kubeApiServer: KubeApiServer, remoteInteraction: RemoteInteraction, remoteEventListener: RemoteEventListener)(implicit ec: ExecutionContext) {

  def registerToTheCluster: Future[Unit] =
    for {
      _ <- kubeApiServer.registersRemoteComponents
      _ <- remoteInteraction.publishesItsInterface
      _ <- remoteEventListener.listensToEvents
    } yield ()
}
