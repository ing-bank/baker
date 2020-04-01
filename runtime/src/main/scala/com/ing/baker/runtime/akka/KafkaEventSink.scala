package com.ing.baker.runtime.akka

import cakesolutions.kafka.KafkaProducer.Conf
import cakesolutions.kafka.{KafkaProducer, KafkaProducerRecord}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.scaladsl.{EventInstance, BakerEvent}
import com.ing.baker.runtime.serialization.EventJsonEncoders._
import com.typesafe.scalalogging.LazyLogging
import io.circe.syntax._
import org.apache.kafka.common.serialization.StringSerializer

trait EventSink {
  def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit]
  def close(): Unit = ()
}

object KafkaEventSink extends LazyLogging {

  def resource(settings: KafkaEventSinkSettings)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, KafkaEventSink] = {

    logger.info(s"Starting Kafka streaming event sink: $settings")

    Resource.make(
      IO {
        new KafkaEventSink(
          KafkaProducer(Conf(new StringSerializer(), new StringSerializer(), settings.`bootstrap-servers`)),
          settings)
      }
    )(sink => IO(sink.close()))
  }
}

class KafkaEventSink(
  kafkaProducer: KafkaProducer[String, String],
  settings: KafkaEventSinkSettings
) extends EventSink with LazyLogging {

  override def close(): Unit = kafkaProducer.close()

  def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit] = {
    (event match {
      case eventInstance: EventInstance =>
        Some(KafkaProducerRecord[String, String](settings.`recipe-events-topic`, None, eventInstance.asJson.noSpaces))
      case bakerEvent: BakerEvent    =>
        Some(KafkaProducerRecord[String, String](settings.`baker-events-topic`, None, bakerEvent.asJson.noSpaces))
      case _                =>
        logger.warn(s"Don't know where to send event of class ${ event.getClass.getSimpleName }: $event")
        None
    }) map { record =>
      IO.fromFuture(IO {
        kafkaProducer.send(record)
      }).map(_ =>  () )
    } getOrElse IO.unit
  }

}