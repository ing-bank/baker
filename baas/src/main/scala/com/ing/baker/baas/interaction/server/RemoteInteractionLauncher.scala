package com.ing.baker.baas.interaction.server

import java.util.concurrent.atomic.AtomicReference

import akka.Done
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.HttpMethods.POST
import akka.http.scaladsl.model.HttpRequest
import akka.http.scaladsl.server.RouteResult
import akka.util.ByteString
import com.ing.baker.baas.server.protocol.AddInteractionHTTPRequest
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.core.InteractionImplementation
import com.ing.baker.runtime.core.internal.MethodInteractionImplementation
import com.ing.baker.types.Type
import org.slf4j.LoggerFactory

import scala.concurrent.duration.{FiniteDuration, _}
import scala.concurrent.{Future, Promise}

case class RemoteInteractionLauncher(ownHost: String,
                                     ownPort: Int,
                                     baasHost: String,
                                     baasPort: Int)(implicit val actorSystem: ActorSystem) extends ClientUtils {

  private var interactionImplementations: Map[String, InteractionImplementation] = Map.empty[String, InteractionImplementation]

  override val log = LoggerFactory.getLogger(classOf[RemoteInteractionLauncher])

  import actorSystem.dispatcher

  val timeout: FiniteDuration = 30 seconds

  private val bindingFuture = new AtomicReference[Future[Http.ServerBinding]]()

  def start(): Future[Done] = {
    log.info(s"Starting remote http server on $ownHost:$ownPort")

    val serverBindingPromise = Promise[Http.ServerBinding]()

    if (bindingFuture.compareAndSet(null, serverBindingPromise.future)) {
      val routes = RouteResult.route2HandlerFlow(new RemoteInteractionRoutes(actorSystem).apply(this))
      val serverFutureBinding = Http().bindAndHandle(routes, ownHost, ownPort)
      serverBindingPromise.completeWith(serverFutureBinding)
      serverBindingPromise.future.map(_ => Done)
    }
    else {
      Future(Done)
    }
  }

  def addImplementation(any: AnyRef): Unit = {
    val methodImplementation: MethodInteractionImplementation = MethodInteractionImplementation(any)
    interactionImplementations = interactionImplementations.+((methodImplementation.name, methodImplementation))
    registerRemoteImplementation(methodImplementation.name, methodImplementation.inputTypes)
  }

  def addImplementation(interactionImplementation: InteractionImplementation): Unit = {
    interactionImplementations = interactionImplementations.+((interactionImplementation.name, interactionImplementation))
    registerRemoteImplementation(interactionImplementation.name, interactionImplementation.inputTypes)
  }

  //TODO change so that it not finds on name but on complete Interaction
  def getImplementation(name: String) : Option[InteractionImplementation] = {
    interactionImplementations.get(name)
  }



  private def registerRemoteImplementation(interactionName: String, inputTypes: Seq[Type]) = {
    //Create the request to Add the interaction implementation to Baas
    log.info("Registering remote implementation client")
    val addInteractionHTTPRequest = AddInteractionHTTPRequest(interactionName, s"http://$ownHost:$ownPort/$interactionName", inputTypes)

    val baseUri: String = s"http://$baasHost:$baasPort"
    val request = HttpRequest(
      uri = s"$baseUri/implementation",
      method = POST,
      entity = ByteString.fromArray(serializer.serialize(addInteractionHTTPRequest).get))

    doRequest(request, logEntity)(actorSystem, materializer, timeout)
  }
}
