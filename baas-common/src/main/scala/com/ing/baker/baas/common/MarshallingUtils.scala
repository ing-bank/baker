package com.ing.baker.runtime.baas

import akka.http.scaladsl.marshalling.{Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.{ContentTypes, HttpResponse, MediaTypes, StatusCodes}
import akka.http.scaladsl.server.{Route, StandardRoute}
import akka.http.scaladsl.server.Directives.{complete, onSuccess}
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshal, Unmarshaller}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap
import com.ing.baker.runtime.common.BakerException
import BaaSProto._
import akka.stream.Materializer

import scala.concurrent.{ExecutionContext, Future}

object MarshallingUtils {

  type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  def completeWithBakerFailures[A, P <: ProtoMessage[P]](f: Future[A])(implicit ec: ExecutionContext, m1: ProtoMap[A, P]): Route =
    complete(f.map(Right(_)).recover { case e: BakerException => Left(BaaSProtocol.BaaSRemoteFailure(e)) })

  def completeWithBakerFailures(f: Future[Unit])(implicit ec: ExecutionContext): Route =
    onSuccess(f.map(_ => None).recover { case e: BakerException => Some(e) }) {
      case Some(e) => complete(BaaSProtocol.BaaSRemoteFailure(e))
      case None => complete(StatusCodes.OK)
    }

  case class UnmarshalWithBakerExceptions[A](response: HttpResponse) {

    def withBakerExceptions[P <: ProtoMessage[P]](implicit ec: ExecutionContext, mat: Materializer, m1: ProtoMap[A, P]): Future[A] = {
      for {
        decoded <- Unmarshal(response).to[Either[BaaSProtocol.BaaSRemoteFailure, A]]
        response <- decoded match {
          case Left(e) => Future.failed(e.error)
          case Right(a) => Future.successful(a)
        }
      } yield response
    }
  }

  def unmarshal[A](response: HttpResponse): UnmarshalWithBakerExceptions[A] =
    UnmarshalWithBakerExceptions[A](response)

  def unmarshalBakerExceptions(response: HttpResponse)(implicit ec: ExecutionContext, mat: Materializer): Future[Unit] =
    response.entity.httpEntity.contentType match {
      case ContentTypes.`application/octet-stream` =>
        Unmarshal(response)
          .to[BaaSProtocol.BaaSRemoteFailure]
          .flatMap(e => Future.failed(e.error))
      case _ =>
        Future.successful(())
    }

  implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)

  implicit def protoEitherMarshaller[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): ToEntityMarshaller[Either[A, B]] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`) {
      case Left(a) => m1.toByteArray(a)
      case Right(b) => m2.toByteArray(b)
    }

  implicit def protoEitherUnmarshaller[A, P0 <: ProtoMessage[P0], B, P1 <: ProtoMessage[P1]](implicit m1: ProtoMap[A, P0], m2: ProtoMap[B, P1]): FromEntityUnmarshaller[Either[A, B]] =
    Unmarshaller.byteArrayUnmarshaller.map { byteArray =>
      m1.fromByteArray(byteArray).map(Left(_)).orElse(m2.fromByteArray(byteArray).map(Right(_))).get
    }
}
