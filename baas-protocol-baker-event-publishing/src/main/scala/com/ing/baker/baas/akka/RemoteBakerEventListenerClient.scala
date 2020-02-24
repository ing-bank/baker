package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshal, Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.model._
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshaller}
import akka.stream.Materializer
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap}

import scala.concurrent.Future

object RemoteBakerEventListenerClient {

  def apply(hostname: String)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) =
    new RemoteBakerEventListenerClient(Uri(hostname))
}

class RemoteBakerEventListenerClient(hostname: Uri)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) {

  import system.dispatcher

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  private implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)


  private val root: Path = Path./("api")./("v3")

  private def withPath(path: Path): Uri = hostname.withPath(path)

  def apply(event: BakerEvent): Future[Unit] =
    for {
      encoded <- Marshal(event).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("apply")), entity = encoded)
      _ <- Http().singleRequest(request)
    } yield ()
}
