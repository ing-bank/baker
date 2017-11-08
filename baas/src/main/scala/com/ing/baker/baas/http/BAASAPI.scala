package com.ing.baker.baas.http

import java.util.concurrent.atomic.AtomicReference

import akka.Done
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.server.{Directives, RouteResult}
import akka.stream.ActorMaterializer
import com.ing.baker.baas.BAAS

import scala.concurrent.{Future, Promise}

class BAASAPI(baas: BAAS,
              host: String,
              port: Int)(implicit actorSystem: ActorSystem) extends Directives {

  private implicit val materializer = ActorMaterializer()

  import actorSystem.dispatcher

  private val bindingFuture = new AtomicReference[Future[Http.ServerBinding]]()

  def start(): Future[Done] = {
    val serverBindingPromise = Promise[Http.ServerBinding]()
    if (bindingFuture.compareAndSet(null, serverBindingPromise.future)) {
      val routes = RouteResult.route2HandlerFlow(
        BAASAPIRoutes(baas))

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