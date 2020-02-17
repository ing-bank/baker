package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.{MediaTypes, StatusCodes}
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshaller}
import akka.stream.Materializer
import com.ing.baker.baas.protocol
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap, SerializersProvider}

import scala.concurrent.Future

object RemoteEventListenerHttp {

  def run(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit)(host: String, port: Int)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): Future[Http.ServerBinding] = {
    import system.dispatcher
    val server = new RemoteEventListenerHttp(listenerFunction)(system, mat, encryption)
    Http().bindAndHandle(server.route, host, port)
  }
}

class RemoteEventListenerHttp(listenerFunction: (RecipeEventMetadata, EventInstance) => Unit)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) {

  import system.dispatcher

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  private implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)

  private implicit def protoEitherUnmarshaller[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): FromEntityUnmarshaller[Either[A, B]] =
    Unmarshaller.byteArrayUnmarshaller.map { byteArray =>
      m1.fromByteArray(byteArray).map(Left(_)).orElse(m2.fromByteArray(byteArray).map(Right(_))).get
    }

  private implicit val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  private def route: Route = concat(pathPrefix("api" / "v3")(concat(health, apply)))

  private def health: Route = pathPrefix("health")(get(complete(StatusCodes.OK)))

  private def apply: Route = post(path("apply") {
    entity(as[protocol.ProtocolDistributedEventPublishing.Event]) { request =>
      Future(listenerFunction(request.recipeEventMetadata, request.event))
      complete(StatusCodes.OK)
    }
  })
}
