package com.ing.baker.baas.akka

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshal, Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.model.headers.RawHeader
import akka.http.scaladsl.model._
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshal, Unmarshaller}
import akka.stream.Materializer
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance}
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap}
import com.ing.baker.types.Type

import scala.concurrent.Future

object RemoteInteractionClient {

  def apply(hostname: String)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) =
    new RemoteInteractionClient(Uri(hostname))
}

class RemoteInteractionClient(hostname: Uri)(implicit system: ActorSystem, mat: Materializer, encryption: Encryption) {

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

  private implicit def protoEitherUnmarshaller[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): FromEntityUnmarshaller[Either[A, B]] =
    Unmarshaller.byteArrayUnmarshaller.map { byteArray =>
      m1.fromByteArray(byteArray).map(Left(_)).orElse(m2.fromByteArray(byteArray).map(Right(_))).get
    }

  private val root: Path = Path./("api")./("v3")

  private def withPath(path: Path): Uri = hostname.withPath(path)

  def interface: Future[(String, Seq[Type])] = {
    val request = HttpRequest(method = HttpMethods.GET, uri = withPath(root./("interface")))
      .withHeaders(RawHeader("X-Bakery-Intent", s"Remote-Interaction:$intendedHost"))
    for {
      response <- Http().singleRequest(request)
      decoded <- Unmarshal(response).to[ProtocolInteractionExecution.InstanceInterface]
    } yield (decoded.name, decoded.input)
  }

  def apply(input: Seq[IngredientInstance]): Future[Option[EventInstance]] =
    for {
      encoded <- Marshal(ProtocolInteractionExecution.ExecuteInstance(input)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("apply")), entity = encoded)
          .withHeaders(RawHeader("X-Bakery-Intent", s"Remote-Interaction:$intendedHost"))
      response <- Http().singleRequest(request)
      decoded <- Unmarshal(response).to[Either[
        ProtocolInteractionExecution.InstanceExecutedSuccessfully,
        ProtocolInteractionExecution.InstanceExecutionFailed]]
      result <- decoded match {
        case Left(result) =>
          Future.successful(result.result)
        case Right(e) =>
          Future.failed(new RuntimeException(s"Remote interaction failed with message: ${e.message}"))
      }
    } yield result
}
