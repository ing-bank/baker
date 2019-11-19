package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import com.ing.baker.baas.akka.EventListenerAgent
import com.ing.baker.baas.protocol
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}

import scala.concurrent.Future

case class BaaSEventListener(actorSystem: ActorSystem) extends protocol.BaaSEventListener[Future] with ScalaApi {

  override type EventInstanceType = EventInstance

  override type RecipeEventMetadataType = RecipeEventMetadata

  override def registerEventListener(recipeName: String, listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Future[Unit] =
    Future.successful { actorSystem.actorOf(EventListenerAgent(recipeName, listenerFunction)) }
}

