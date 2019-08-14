package com.ing.baker.baas.interaction.http

import java.util.concurrent.atomic.AtomicReference

import akka.Done
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.RouteResult
import akka.stream.ActorMaterializer
import com.ing.baker.baas.BAASClient
import com.ing.baker.runtime.core.InteractionImplementation
import org.slf4j.LoggerFactory

import scala.concurrent.{Future, Promise}


case class RemoteInteractionLauncher(implementations: Map[String, InteractionImplementation],
                                     hostname: String,
                                     port: Int)(implicit val actorSystem: ActorSystem) {

  val log = LoggerFactory.getLogger(classOf[RemoteInteractionLauncher])

  import actorSystem.dispatcher
  implicit val materializer = ActorMaterializer()(actorSystem)

  private val bindingFuture = new AtomicReference[Future[Http.ServerBinding]]()

  def start(): Future[Done] = {
    log.info(s"Starting remote http server on $hostname:$port for interactions: ${implementations.keys.mkString(",")}")

    val serverBindingPromise = Promise[Http.ServerBinding]()

    if (bindingFuture.compareAndSet(null, serverBindingPromise.future)) {
      val routes = RouteResult.route2HandlerFlow(RemoteInteractionRoutes(implementations))
      val serverFutureBinding = Http().bindAndHandle(routes, hostname, port)
      serverBindingPromise.completeWith(serverFutureBinding)
      serverBindingPromise.future.map(_ => Done)
    }
    else {
      Future(Done)
    }
  }

  def registerToBaker(baker: BAASClient) = {
    implementations.foreach {
      case (name, implementation) => baker.addRemoteImplementation(name, s"http://$hostname:$port/$name", implementation.inputTypes)
    }
  }
}


