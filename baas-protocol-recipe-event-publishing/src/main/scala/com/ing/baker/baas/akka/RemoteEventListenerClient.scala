package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshal, Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.model._
import akka.http.scaladsl.model.headers.RawHeader
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshaller}
import akka.stream.Materializer
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap, SerializersProvider}

import scala.concurrent.Future

object RemoteEventListenerClient {

  def apply(hostname: String)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) =
    new RemoteEventListenerClient(Uri(hostname))
}

class RemoteEventListenerClient(hostname: Uri)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) {

  import system.dispatcher

  val intendedHost: String = hostname.authority.host.toString()

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  private implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)

  private implicit def protoEitherMarshaller[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): ToEntityMarshaller[Either[A, B]] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`) {
      case Left(a) => m1.toByteArray(a)
      case Right(b) => m2.toByteArray(b)
    }

  private implicit val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  private val root: Path = Path./("api")./("v3")

  private def withPath(path: Path): Uri = hostname.withPath(path)

  def apply(recipeEventMetadata: RecipeEventMetadata, event: EventInstance): Future[Unit] =
    for {
      encoded <- Marshal(ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("apply")), entity = encoded)
        .withHeaders(RawHeader("X-Bakery-Intent", s"Remote-Event-Listener:$intendedHost"))
      _ = println(Console.GREEN + request + Console.RESET)
      response <- Http().singleRequest(request)
      _ = println(Console.GREEN + response + Console.RESET)
    } yield ()
}
