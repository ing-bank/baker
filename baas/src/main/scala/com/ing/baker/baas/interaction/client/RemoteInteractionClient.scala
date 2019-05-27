package com.ing.baker.baas.interaction.client

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpRequest
import com.ing.baker.baas.interaction.server.protocol.{ExecuteInteractionHTTPRequest, ExecuteInteractionHTTPResponse}
import com.ing.baker.baas.util.ClientUtils
import com.ing.baker.runtime.common.InteractionImplementation
import com.ing.baker.runtime.scaladsl.RuntimeEvent
import com.ing.baker.types.{Type, Value}
import org.slf4j.LoggerFactory

import scala.concurrent.{Await, Future}
import scala.concurrent.duration.{FiniteDuration, _}

//This is the interactionImplementation as running in the BAAS cluster
//This communicates with a RemoteInteractionImplementationClient that execute the request.
case class RemoteInteractionClient(override val name: String,
                                   uri: String,
                                   override val inputTypes: Seq[Type])(implicit val actorSystem: ActorSystem) extends InteractionImplementation with ClientUtils {

  override val log = LoggerFactory.getLogger(classOf[RemoteInteractionClient])

  implicit val timout: FiniteDuration = 30 seconds

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  override def execute(input: Seq[Value]): Future[Option[RuntimeEvent]] = {

    log.info(s"Calling remote execution of interaction: $name on $uri")

    val request = ExecuteInteractionHTTPRequest(input)

    val httpRequest = HttpRequest(
        uri = s"$uri/execute",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = serializer.serialize(request).get)
    //
    doRequestAndParseResponse[ExecuteInteractionHTTPResponse](httpRequest).map(_.runtimeEventOptional)(actorSystem.dispatcher)
  }
}
