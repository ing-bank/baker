package com.ing.baker.baas.interaction.client

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpRequest
import com.ing.baker.baas.interaction.server.protocol.{ExecuteInteractionHTTPRequest, ExecuteInteractionHTTPResponse}
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.types.Type

import scala.concurrent.duration.FiniteDuration

/** This is the interactionImplementation as running in the BAAS cluster
  * This communicates with a RemoteInteractionImplementationClient that execute the request.
  */
object RemoteInteractionClient {

  def apply(name: String, uri: String, inputIngredients: Seq[Type])(implicit system: ActorSystem, duration: FiniteDuration): InteractionInstance = {
    val utils = new ClientUtils { override implicit val actorSystem: ActorSystem = system }
    import system.dispatcher
    import utils.materializer
    InteractionInstance(
      name = name,
      input = inputIngredients,
      output = None,
      run = input => {
        utils.log.info(s"Calling remote execution of interaction: $name on $uri")
        val request = ExecuteInteractionHTTPRequest(input)
        val httpRequest = HttpRequest(
          uri = s"$uri/execute",
          method = akka.http.scaladsl.model.HttpMethods.POST,
          entity = utils.serializer.serialize(request).get)
        //
        utils.doRequestAndParseResponse[ExecuteInteractionHTTPResponse](httpRequest).map(_.runtimeEventOptional)
      }
    )
  }
}
