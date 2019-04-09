package com.ing.baker.baas.server

import java.util.concurrent.atomic.AtomicReference

import akka.Done
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.{Directives, RouteResult}
import akka.stream.ActorMaterializer
import com.ing.baker.runtime.core.Baker

import scala.concurrent.{Future, Promise}

class BaasServer(baker: Baker,
                 host: String,
                 port: Int)(implicit actorSystem: ActorSystem) extends Directives {

  private implicit val materializer: ActorMaterializer = ActorMaterializer()

  import actorSystem.dispatcher

  private val bindingFuture = new AtomicReference[Future[Http.ServerBinding]]()

  def start(): Future[Done] = {
    val serverBindingPromise = Promise[Http.ServerBinding]()
    if (bindingFuture.compareAndSet(null, serverBindingPromise.future)) {
      val routes = RouteResult.route2HandlerFlow(
        new BaasRoutes(actorSystem).apply(baker))

      val serverFutureBinding = Http().bindAndHandle(routes, host, port)

      serverBindingPromise.completeWith(serverFutureBinding)
      serverBindingPromise.future.map(_ => Done)
    }

    else {
      Future(Done)
    }
  }

  def stop(): Future[Done] =
    if (bindingFuture.get() == null) {
      Future(Done)
    } else {
      val stopFuture = bindingFuture.get().flatMap(_.unbind()).map(_ => Done)
      bindingFuture.set(null)
      stopFuture
    }
}