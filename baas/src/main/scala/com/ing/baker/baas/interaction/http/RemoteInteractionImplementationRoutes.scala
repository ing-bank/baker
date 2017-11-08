package com.ing.baker.baas.interaction.http

import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.runtime.core.interations.InteractionImplementation
import org.slf4j.LoggerFactory

class RemoteInteractionImplementationRoutes{}

object RemoteInteractionImplementationRoutes extends Directives {

  val log = LoggerFactory.getLogger(classOf[RemoteInteractionImplementationRoutes])

  def apply(interactionImplementation: InteractionImplementation): Route = {
    val baasRoutes = {
      path(interactionImplementation.name) {
        post {
          entity(as[ByteString]) { string =>
            log.info(s"interaction implementation called for: ${interactionImplementation.name}")
            val byteArray: Array[Byte] = string.toArray
            //Get the request opbject
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[ExecuteInteractionHTTPRequest]
            try {
              log.info(s"Executing interaction: ${interactionImplementation.name}")
              val runtimeEvent = interactionImplementation.execute(request.interaction, request.input)
              log.info(s"Interaction executed: ${interactionImplementation.name}")
              complete(kryoPool.toBytesWithClass(runtimeEvent))
            } catch {
              case e: Exception => {
                println(s"Exception when adding recipe: ${e.getMessage}")
                throw e
              }
            }
          }
        }
      }
    }
    baasRoutes
  }
}