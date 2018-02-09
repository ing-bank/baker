package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.persistence.journal.{EventAdapter, EventSeq}
import akka.serialization.{SerializationExtension, Serializer}
import org.slf4j.LoggerFactory

class ProtoSerializationCheckerEventAdapter(system: ExtendedActorSystem) extends EventAdapter {

  private val logger = LoggerFactory.getLogger(classOf[ProtoSerializationCheckerEventAdapter])

  private lazy val serialization = SerializationExtension.get(system)

  private def getSerializerFor(obj: AnyRef): Serializer = serialization.findSerializerFor(obj)

  override def manifest(event: Any): String =
    "" // when no manifest needed, return ""

  override def toJournal(event: Any): Any = {
    val serializer = getSerializerFor(event.asInstanceOf[AnyRef])

    if (!serializer.isInstanceOf[BakerProtobufSerializer] && !serializer.isInstanceOf[ScalaPBSerializer]) {
      val message = s"Unsupported serializer $serializer used during persistence of event $event"
      logger.error(message)
      throw new RuntimeException(message)
    }

    event
  }

  override def fromJournal(event: Any, manifest: String): EventSeq =
    EventSeq.single(event) // identity
}