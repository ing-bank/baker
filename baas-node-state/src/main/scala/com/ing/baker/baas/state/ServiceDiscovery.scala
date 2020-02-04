package com.ing.baker.baas.state

import scala.concurrent.Future

trait ServiceDiscovery {

  def getInteractionAddresses: Future[Seq[String]]

  def getEventListenersAddresses: Future[Seq[(String, String)]]
}

