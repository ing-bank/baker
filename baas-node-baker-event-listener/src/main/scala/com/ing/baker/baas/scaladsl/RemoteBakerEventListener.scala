package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.akka.RemoteBakerEventListenerHttp
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

object RemoteBakerEventListener extends common.RemoteBakerEventListener[Future] with ScalaApi {

  override type BakerEventType = BakerEvent

  private[baas] def runWith(listenerFunction: BakerEvent => Unit, port: Int, timeout: FiniteDuration)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): Future[Http.ServerBinding] = {
    import system.dispatcher
    RemoteBakerEventListenerHttp.run(listenerFunction)( "0.0.0.0", port).map { hook =>
      sys.addShutdownHook(Await.result(hook.unbind(), timeout))
      hook
    }
  }

  override def load(listenerFunction: BakerEvent => Unit): Unit = {
    val timeout: FiniteDuration = 20.seconds
    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")
    implicit val system: ActorSystem = ActorSystem("RemoteBakerEventListenerSystem")
    implicit val materializer: Materializer = ActorMaterializer()(system)
    implicit val encryption: Encryption = Encryption.from(config)
    Await.result(runWith(listenerFunction, port, timeout), timeout)
  }
}

