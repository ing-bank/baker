package com.ing.baker.baas.recipelistener

import cats.data.EitherT
import cats.effect.IO
import com.ing.baker.runtime.serialization.ProtoMap
import org.http4s.EntityDecoder.collectBinary
import org.http4s.util.CaseInsensitiveString
import org.http4s.{EntityDecoder, EntityEncoder, Header, MalformedMessageBodyFailure, MediaType, Uri}

import scala.util.{Failure, Success}

object BakeryHttp {

  object ProtoEntityEncoders {

    type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

    implicit def protoDecoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityDecoder[IO, A] =
      EntityDecoder.decodeBy(MediaType.application.`octet-stream`)(collectBinary[IO]).map(_.toArray)
        .flatMapR { bytes =>
          protoMap.fromByteArray(bytes) match {
            case Success(a) =>
              EitherT.fromEither[IO](Right(a))
            case Failure(exception) =>
              EitherT.fromEither[IO](Left(MalformedMessageBodyFailure(exception.getMessage, Some(exception))))
          }
        }

    implicit def protoEncoder[A, P <: ProtoMessage[P]](implicit protoMap: ProtoMap[A, P]): EntityEncoder[IO, A] =
      EntityEncoder.byteArrayEncoder[IO].contramap(protoMap.toByteArray)
  }

  object Headers {

    def `X-Bakery-Intent`(intent: Intent, hostname: Uri): Header = {
      Header.Raw(CaseInsensitiveString("X-Bakery-Intent"), intent.render(hostname))
    }

    sealed abstract class Intent(rawIntent: String) {

      def render(hostname: Uri): String = {
        val intendedHost = hostname.authority.map(_.host.value).getOrElse("unknown")
        s"$rawIntent:$intendedHost"
      }
    }

    object Intent {

      case object `Remote-Event-Listener` extends Intent("Remote-Event-Listener")

      case object `Remote-Baker-Event-Listener` extends Intent("Remote-Baker-Event-Listener")

      case object `Remote-Interaction` extends Intent("Remote-Interaction")
    }
  }
}
