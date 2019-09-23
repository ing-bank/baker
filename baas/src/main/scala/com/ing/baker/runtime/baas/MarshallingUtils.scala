package com.ing.baker.runtime.baas

import akka.http.scaladsl.marshalling.{Marshaller, ToEntityMarshaller}
import akka.http.scaladsl.model.{ContentTypes, MediaTypes}
import akka.http.scaladsl.unmarshalling.{FromEntityUnmarshaller, Unmarshaller}
import com.ing.baker.runtime.akka.actor.serialization.ProtoMap

object MarshallingUtils {

  type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  implicit def protoMarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): ToEntityMarshaller[A] =
    Marshaller.ByteArrayMarshaller.wrap(MediaTypes.`application/octet-stream`)(mapping.toByteArray)

  implicit def protoUnmarshaller[A, P <: ProtoMessage[P]](implicit mapping: ProtoMap[A, P]): FromEntityUnmarshaller[A] =
    Unmarshaller.byteArrayUnmarshaller.map(mapping.fromByteArray(_).get)
}
