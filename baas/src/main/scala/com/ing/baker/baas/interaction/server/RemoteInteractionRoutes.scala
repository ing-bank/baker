package com.ing.baker.baas.interaction.server

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import com.ing.baker.baas.interaction.server.protocol._
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.akka.RuntimeEvent
import org.slf4j.LoggerFactory

import scala.concurrent.Future


class RemoteInteractionRoutes(override val actorSystem: ActorSystem) extends Directives with ClientUtils {

  import actorSystem.dispatcher

  override val log = LoggerFactory.getLogger(this.getClass.getName)

  def apply(remoteInteractionLauncher: RemoteInteractionLauncher): Route = {
    val baasRoutes = {
      pathPrefix(Segment) { interactionName =>

        val implementationOptional = remoteInteractionLauncher.getImplementation(interactionName)

        if(implementationOptional.isEmpty) {
          log.error(s"No implementation found for: $interactionName")
          throw new IllegalArgumentException(s"No such interaction: $interactionName")
        }

        path("execute") {
          post {
            entity(as[ExecuteInteractionHTTPRequest]) { executeInteractionHTTPRequest =>

              log.info(s"interaction implementation called for: $interactionName")

              log.info(s"Executing interaction: $interactionName")

              val runtimeEventOptional: Future[Option[RuntimeEvent]] = implementationOptional.get.execute(executeInteractionHTTPRequest.input)

              log.info(s"Interaction executed: $interactionName")

              complete(runtimeEventOptional.map(ExecuteInteractionHTTPResponse(_)))
            }
          }
        } ~
        path("keepalive") {
          get {
            complete("OK")
          }
        } ~
        path("input") {
          get {
            complete("")
          }
        }
      }
    }

    baasRoutes
  }
}