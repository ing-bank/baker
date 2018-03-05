package com.ing.baker.baas.interaction.http

import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.KryoUtil.defaultKryoPool
import com.ing.baker.baas.http.BaasMarshalling
import com.ing.baker.runtime.core.interations.InteractionImplementation
import org.slf4j.LoggerFactory


object RemoteInteractionRoutes extends Directives with BaasMarshalling {

  val log = LoggerFactory.getLogger(RemoteInteractionRoutes.getClass.getName)

  def apply(implementations: Map[String, InteractionImplementation]): Route = {
    val baasRoutes = {
      pathPrefix(Segment) { interactionName =>

        val implementation = implementations.getOrElse(interactionName, throw new IllegalArgumentException(s"No such interaction: $interactionName"))

        path("execute") {
          post {
            entity(as[ByteString]) { string =>

              log.info(s"interaction implementation called for: ${interactionName}")

              val byteArray: Array[Byte] = string.toArray
              val request = kryoPool.fromBytes(byteArray).asInstanceOf[ExecuteInteractionHTTPRequest]

              log.info(s"Executing interaction: $interactionName")

              val runtimeEvent = implementation.execute(request.interaction, request.input).orNull

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