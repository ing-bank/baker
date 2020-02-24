package com.ing.baker.baas.recipelistener

import cats.data.EitherT
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import org.http4s.Method._
import org.http4s.{EntityDecoder, EntityEncoder, Header, MalformedMessageBodyFailure, MediaRange, MediaType, Status, Uri, headers}
import org.http4s.client.Client
import org.http4s.client.dsl.io._
import com.ing.baker.baas.protocol.DistributedEventPublishingProto._
import com.ing.baker.baas.protocol.ProtocolDistributedEventPublishing
import com.ing.baker.runtime.scaladsl.{EventInstance, RecipeEventMetadata}
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap}
import org.http4s.EntityDecoder.collectBinary
import org.http4s.util.CaseInsensitiveString

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

  val XBakeryIntent: Header = {
    val intendedHost = hostname.authority.map(_.host.value).getOrElse("unknown")
    Header.Raw(CaseInsensitiveString("X-Bakery-Intent"), s"Remote-Event-Listener:$intendedHost")
  }

  def apply(recipeEventMetadata: RecipeEventMetadata, event: EventInstance): IO[Unit] = {
    val request = POST(
      ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event),
      hostname / "api" / "v3" / "apply",
      XBakeryIntent
    )
    client.use(_.status(request)).void
  }

}
