package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.akka.RemoteEventListenerHttp
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

object RemoteEventListener extends common.RemoteEventListener[Future] with ScalaApi {

  override type EventInstanceType = EventInstance

  override type RecipeEventMetadataType = RecipeEventMetadata

  private[baas] def runWith(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit, port: Int, timeout: FiniteDuration)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): Future[Http.ServerBinding] = {
    // Temp
    println(Console.YELLOW + s"Starting remote interaction [${listenerFunction.toString}]" + Console.RESET)
    // Temp
    println(Console.YELLOW + s"Starting the http server on port $port" + Console.RESET)
    import system.dispatcher
    RemoteEventListenerHttp.run(listenerFunction)( "0.0.0.0", port).map { hook =>
      println(Console.GREEN + "Http server started" + Console.RESET)
      println(hook.localAddress)
      sys.addShutdownHook(Await.result(hook.unbind(), timeout))
      hook
    }
  }

  override def load(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit): Unit = {
    val timeout: FiniteDuration = 20.seconds
    val config = ConfigFactory.load()
    val port = config.getInt("baas-component.http-api-port")
    implicit val system: ActorSystem = ActorSystem("RemoteEventListenerSystem")
    implicit val materializer: Materializer = ActorMaterializer()(system)
    implicit val encryption: Encryption = Encryption.from(config)
    Await.result(runWith(listenerFunction, port, timeout), timeout)
  }
}

