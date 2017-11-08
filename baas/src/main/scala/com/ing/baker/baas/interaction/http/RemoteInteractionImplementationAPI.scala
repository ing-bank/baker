package com.ing.baker.baas.interaction.http

import java.util.concurrent.atomic.AtomicReference

import akka.Done
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.RouteResult
import akka.stream.ActorMaterializer
import com.ing.baker.runtime.core.interations.InteractionImplementation
import org.slf4j.LoggerFactory

import scala.concurrent.{Future, Promise}

case class RemoteInteractionImplementationAPI(InteractionImplementation: InteractionImplementation,
                                              hostname: String,
                                              port: Int) {
  val log = LoggerFactory.getLogger(classOf[RemoteInteractionImplementationAPI])

  implicit val defaultActorSystem = ActorSystem()
  import defaultActorSystem.dispatcher
  implicit val materializer = ActorMaterializer()(defaultActorSystem)

  private val bindingFuture = new AtomicReference[Future[Http.ServerBinding]]()

  def start(): Future[Done] = {
    log.info(s"Starting remote interaction implementation for: ${InteractionImplementation.name} ")
    val serverBindingPromise = Promise[Http.ServerBinding]()
    if (bindingFuture.compareAndSet(null, serverBindingPromise.future)) {
      val routes = RouteResult.route2HandlerFlow(
        RemoteInteractionImplementationRoutes(InteractionImplementation))
      val serverFutureBinding = Http().bindAndHandle(routes, hostname, port)
      serverBindingPromise.completeWith(serverFutureBinding)
      serverBindingPromise.future.map(_ => Done)
    }
    else {
      Future(Done)
    }
  }

}


