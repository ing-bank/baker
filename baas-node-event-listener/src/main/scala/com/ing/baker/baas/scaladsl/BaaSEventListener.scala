package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import com.ing.baker.baas.akka.EventListenerAgent
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.EventInstance

import scala.concurrent.Future

case class BaaSEventListener(actorSystem: ActorSystem) extends common.BaaSEventListener[Future] with ScalaApi {

  override type EventInstanceType = EventInstance

  override def registerEventListener(recipeName: String, listenerFunction: (String, EventInstance) => Unit): Future[Unit] =
    Future.successful { actorSystem.actorOf(EventListenerAgent(recipeName, listenerFunction)) }
}

