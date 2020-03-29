package com.ing.baker.runtime.akka

import java.util.Properties

import akka.actor.ActorSystem
import akka.stream.Materializer
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBakerConfig.{EventSinkSettings, KafkaEventSinkSettings}
import com.ing.baker.runtime.common.{BakerEvent, EventInstance}
import com.ing.baker.runtime.scaladsl.RecipeEventMetadata
import com.typesafe.scalalogging.LazyLogging
import org.apache.kafka.clients.producer.{KafkaProducer, ProducerRecord}

class EventKafkaProducer(kafkaConfig: KafkaEventSinkSettings)(implicit contextShift: ContextShift[IO], timer: Timer[IO]) extends LazyLogging {

  val props = new Properties()
  props.put("bootstrap.servers", kafkaConfig.`bootstrap-servers`)
  props.put("key.serializer", "org.apache.kafka.common.serialization.StringSerializer")
  props.put("value.serializer", "org.apache.kafka.common.serialization.StringSerializer")
  // todo other producer settings from kafkaConfig? (batch, timeout etc.)

  val producer = new KafkaProducer[String, String](props)

  private def send( topic: String, event: Any): Unit = {

    // todo provisional toString serialisation
    val record = new ProducerRecord[String, String](topic, event.toString)
    logger.info(s"Sending $record to kafka")
    producer.send(record)
  }

  def send(event: Any): Unit = {
    event match {
      case _: BakerEvent =>
        send(kafkaConfig.`bakery-events-topic`, event)
      case _: EventInstance | _: RecipeEventMetadata  =>
        send(kafkaConfig.`recipe-events-topic`, event)
      case _ =>
      logger.warn(s"Don't know where to send event of class ${event.getClass.getSimpleName}: $event")
    }
  }

  def close(): Unit = producer.close()

}

object KafkaEventSink extends LazyLogging {

  def resource(eventSinkSettings: EventSinkSettings)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, KafkaEventSink] = {

    val kafkaEventSinkSettings = eventSinkSettings.kafka
    logger.info(kafkaEventSinkSettings.map(s => s"Starting Kafka streaming event sink: $s").getOrElse("Kafka event sink disabled"))

    Resource.make(
      IO.delay(new KafkaEventSink(eventSinkSettings.kafka.map(config => new EventKafkaProducer(config))))
    )(producer => IO { producer.kafkaProducer.foreach(_.close()) })
  }

}

trait EventSink {
  def fire(event: Any): Unit
}

class KafkaEventSink(
  val kafkaProducer: Option[EventKafkaProducer]
) extends EventSink {
  def fire(event: Any): Unit = {
    kafkaProducer.foreach(_.send(event))
  }
}