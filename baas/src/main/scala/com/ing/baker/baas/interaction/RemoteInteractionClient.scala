package com.ing.baker.baas.interaction

import akka.actor.ActorSystem
import akka.http.scaladsl.model.HttpRequest
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.baas.KryoUtil.defaultKryoPool
import com.ing.baker.baas.ClientUtils._
import com.ing.baker.baas.interaction.http.ExecuteInteractionHTTPRequest
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.core.RuntimeEvent
import com.ing.baker.runtime.core.interations.InteractionImplementation
import com.ing.baker.types.{Type, Value}
import org.slf4j.LoggerFactory

import scala.concurrent.duration._

//This is the interactionImplementation as running in the BAAS cluster
//This communicates with a RemoteInteractionImplementationClient that execute the request.
case class RemoteInteractionClient(override val name: String,
                                   uri: String,
                                   override val inputTypes: Seq[Type])(implicit val actorSystem: ActorSystem) extends InteractionImplementation {

  val log = LoggerFactory.getLogger(classOf[RemoteInteractionClient])

  implicit val timout: FiniteDuration = 30 seconds
  implicit val materializer = ActorMaterializer()

  /**
    * Executes the interaction.
    *
    * TODO input could be map instead of sequence??
    *
    * @param input
    * @return
    */
  override def execute(interaction: InteractionTransition[_], input: Seq[Value]): Option[RuntimeEvent] = {

    log.info(s"Calling remote execution of interaction: $name on $uri")

    val request = ExecuteInteractionHTTPRequest(interaction, input)

    val httpRequest = HttpRequest(
        uri = s"$uri/execute",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(defaultKryoPool.toBytesWithClass(request)))

    Option(doRequestAndParseResponse[RuntimeEvent](httpRequest))
  }
}
