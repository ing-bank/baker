package com.ing.baker.baas.bakerlistener

import cakesolutions.kafka.KafkaProducer.Conf
import cakesolutions.kafka.{KafkaProducer, KafkaProducerRecord}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.ing.baker.runtime.serialization.BakerEventEncoders._
import com.typesafe.config.ConfigFactory
import io.circe.syntax._
import org.apache.kafka.clients.producer.RecordMetadata
import org.apache.kafka.common.serialization.StringSerializer


object RemoteBakerEventListenerClient {

  private val kafkaClientConfigPath: String = "kafka-client"

  /** use method `use` of the Resource, the client will be acquired and shut down automatically each time
    * the resulting `IO` is run, each time using the common connection pool.
    */
  def resource(topic: String)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, KafkaProducer[String, String]] = {
    val conf = ConfigFactory.load().getConfig(kafkaClientConfigPath)
    val producer = IO(KafkaProducer(Conf(conf, new StringSerializer(), new StringSerializer())))

    Resource.make(producer)(resource => IO(resource.close()))
  }
}

final class RemoteBakerEventListenerClient(client: KafkaProducer[String, String], topic: String) {

  def fireEvent(event: BakerEvent)(implicit cs: ContextShift[IO]): IO[RecordMetadata] = {
    val record = KafkaProducerRecord[String, String](topic, None, event.asJson.noSpaces)
    IO.fromFuture(IO(client.send(record)))
  }
}
