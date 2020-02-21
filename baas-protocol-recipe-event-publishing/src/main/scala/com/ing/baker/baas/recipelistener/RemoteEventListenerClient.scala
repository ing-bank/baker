package com.ing.baker.baas.recipelistener

import cats.data.EitherT
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import org.http4s.Method._
import org.http4s.client.Client
import org.http4s.client.dsl.io._
import org.http4s.{DecodeFailure, EntityDecoder, EntityEncoder, MalformedMessageBodyFailure, MediaRange, MediaType, Status, Uri}
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap, AkkaSerializerProvider}
import org.http4s.EntityDecoder.collectBinary

import scala.util.{Failure, Success}

class RemoteEventListenerClient(client: Resource[IO, Client[IO]], hostname: Uri)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private implicit def protoDecoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityDecoder[IO, A] =
    EntityDecoder.decodeBy(MediaType.application.`octet-stream`)(collectBinary[IO]).map(_.toArray)
      .flatMapR { bytes =>
        protoMap.fromByteArray(bytes) match {
          case Success(a) =>
            EitherT.fromEither[IO](Right(a))
          case Failure(exception) =>
            EitherT.fromEither[IO](Left(MalformedMessageBodyFailure(exception.getMessage, Some(exception))))
        }
    }

  private implicit def protoEitherDecoder[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): EntityDecoder[IO, Either[A, B]] =
    protoDecoder[A, P0].map(Left(_)).orElse(protoDecoder[B, P1].map(Right(_)))

  private implicit def protoEncoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityEncoder[IO, A] =
    EntityEncoder.byteArrayEncoder[IO].contramap(protoMap.toByteArray)

  val intendedHost: String = hostname.authority.map(_.host.value).getOrElse("unknown")

  /*
  private implicit val serializersProvider: SerializersProvider =
    SerializersProvider(system, encryption)

  private val root: Path = Path./("api")./("v3")

  private def withPath(path: Path): Uri = hostname.withPath(path)

  def apply(recipeEventMetadata: RecipeEventMetadata, event: EventInstance): Future[Unit] =
    for {
      encoded <- Marshal(ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event)).to[MessageEntity]
      request = HttpRequest(method = HttpMethods.POST, uri = withPath(root./("apply")), entity = encoded)
        .withHeaders(RawHeader("X-Bakery-Intent", s"Remote-Event-Listener:$intendedHost"))
      response <- Http().singleRequest(request)
    } yield ()
   */
}
