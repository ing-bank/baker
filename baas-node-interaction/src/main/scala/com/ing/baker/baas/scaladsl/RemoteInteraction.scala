package com.ing.baker.baas.scaladsl

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.stream.{ActorMaterializer, Materializer}
import com.ing.baker.baas.akka.RemoteInteractionHttp
import com.ing.baker.baas.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.{Config, ConfigFactory}

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

object RemoteInteraction extends common.RemoteInteraction[Future] with ScalaApi {

  override type InteractionInstanceType = InteractionInstance

  def runWith(implementation: InteractionInstance, port: Int, timeout: FiniteDuration)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): Future[Http.ServerBinding] = {
    // Temp
    println(Console.YELLOW + s"Starting remote interaction [${implementation.name}]" + Console.RESET)
    // Temp
    println(Console.YELLOW + s"Starting the http server on port $port" + Console.RESET)
    import system.dispatcher
    RemoteInteractionHttp.run(implementation)( "0.0.0.0", port).map { hook =>
      println(Console.GREEN + "Http server started" + Console.RESET)
      println(hook.localAddress)
      sys.addShutdownHook(Await.result(hook.unbind(), timeout))
      hook
    }
  }

  override def load(implementation: InteractionInstance): Unit = {
    val timeout: FiniteDuration = 20.seconds
    val config = ConfigFactory.load()
    val systemName = config.getString("service.actorSystemName")
    val port = config.getInt("service.httpServerPort")
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()(system)
    // TODO load correct encryption from config
    implicit val encryption: Encryption = Encryption.NoEncryption
    Await.result(runWith(implementation, port, timeout), timeout)
  }
}

