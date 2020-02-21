package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.{MediaTypes, StatusCodes}
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshaller}
import akka.stream.Materializer
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap}

import scala.concurrent.Future

object RemoteBakerEventListenerHttp {

  def run(listenerFunction: BakerEvent => Unit)(host: String, port: Int)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption): Future[Http.ServerBinding] = {
    import system.dispatcher
    val server = new RemoteBakerEventListenerHttp(listenerFunction)(system, mat, encryption)
    Http().bindAndHandle(server.route, host, port)
  }
}

class RemoteBakerEventListenerHttp(listenerFunction: BakerEvent => Unit)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) {

  import system.dispatcher

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  private implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)

  private def route: Route = concat(pathPrefix("api" / "v3")(concat(health, apply)))

  private def health: Route = pathPrefix("health")(get(complete(StatusCodes.OK)))

  private def apply: Route = post(path("apply") {
    entity(as[BakerEvent]) { event =>
      Future(listenerFunction(event))
      complete(StatusCodes.OK)
    }
  })
}
