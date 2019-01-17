package com.ing.baker.baas.interaction.http

import akka.actor.ActorSystem
import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.http.ClientUtils
import com.ing.baker.baas.interaction.protocol._
import com.ing.baker.runtime.core.InteractionImplementation
import org.slf4j.LoggerFactory


class RemoteInteractionRoutes(override val actorSystem: ActorSystem) extends Directives with ClientUtils {

  override val log = LoggerFactory.getLogger(this.getClass.getName)

  def apply(implementations: Map[String, InteractionImplementation]): Route = {
    val baasRoutes = {
      pathPrefix(Segment) { interactionName =>

        val implementation = implementations.getOrElse(interactionName, throw new IllegalArgumentException(s"No such interaction: $interactionName"))

        path("execute") {
          post {
            entity(as[ExecuteInteractionHTTPRequest]) { executeInteractionHTTPRequest =>

              log.info(s"interaction implementation called for: ${interactionName}")

              log.info(s"Executing interaction: $interactionName")

              val runtimeEvent = implementation.execute(executeInteractionHTTPRequest.input).orNull

              log.info(s"Interaction executed: ${interactionName}")

              complete(runtimeEvent)
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