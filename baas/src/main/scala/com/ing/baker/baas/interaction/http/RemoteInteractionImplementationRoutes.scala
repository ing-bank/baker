package com.ing.baker.baas.interaction.http

import akka.http.scaladsl.server.{Directives, Route}
import akka.util.ByteString
import com.ing.baker.baas.BAAS.kryoPool
import com.ing.baker.runtime.core.interations.InteractionImplementation

object RemoteInteractionImplementationRoutes extends Directives {

  def apply(interactionImplementation: InteractionImplementation): Route = {
    val baasRoutes = {
      path(interactionImplementation.name) {
        post {
          entity(as[ByteString]) { string =>
            val byteArray: Array[Byte] = string.toArray
            //Get the request opbject
            val request = kryoPool.fromBytes(byteArray).asInstanceOf[ExecuteInteractionHTTPRequest]
            try {
              val runtimeEvent = interactionImplementation.execute(request.interaction, request.input)
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