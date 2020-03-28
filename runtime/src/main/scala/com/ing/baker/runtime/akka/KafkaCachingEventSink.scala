package com.ing.baker.runtime.akka

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBakerConfig.{EventSinkSettings, KafkaEventSinkSettings}
import com.typesafe.scalalogging.LazyLogging

import scala.collection.mutable
import scala.collection.mutable.Queue

class EventKafkaProducer(kafkaConfig: KafkaEventSinkSettings)(implicit contextShift: ContextShift[IO], timer: Timer[IO]) {

  def send(event: Any): Unit = {
    println(event)
  }

}

object KafkaCachingEventSink extends LazyLogging {

  def resource(eventSinkSettings: EventSinkSettings)(implicit contextShift: ContextShift[IO], timer: Timer[IO], actorSystem: ActorSystem, materializer: Materializer): Resource[IO, KafkaCachingEventSink] = {

    Resource.make(
      IO.delay(new KafkaCachingEventSink(Queue.empty,  eventSinkSettings.kafka.map(config => new EventKafkaProducer(config))))
    )(_ => IO.unit)
  }

}

trait EventSink {
  def fire(event: Any): Unit
  def lastEvents: Seq[String]
}

class KafkaCachingEventSink(
  val lastEvents: mutable.Queue[String],
  kafkaProducer: Option[EventKafkaProducer]
) extends EventSink {
  def fire(event: Any): Unit = {
    lastEvents.enqueue(event.toString)
    kafkaProducer.foreach(_.send(event))
  }
}