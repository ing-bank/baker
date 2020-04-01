package com.ing.baker.kafkalistener

import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.runtime.serialization.EventJsonToScalaDslDecoders
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import fs2.kafka._
import io.circe.{Decoder, Json, ParsingFailure}
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import io.circe.parser._

import scala.concurrent.duration._

object Main extends IOApp with LazyLogging {

  case class KafkaListenerConfig(
    bootstrapServers: String,
    group: String,
    `recipe-events-topic`: String,
    `baker-events-topic`: String,
    `event-processor-class`: String
  )


  override def run(args: List[String]): IO[ExitCode] = {

    val clientConfig = ConfigFactory.load().getConfig("baas-kafka-listener").as[KafkaListenerConfig]

    val eventProcessor = Class.forName(clientConfig.`event-processor-class`).getConstructor().newInstance().asInstanceOf[EventProcessor]

    val bakerEventsDecoder = EventJsonToScalaDslDecoders.bakerEventDecoder
    val eventInstanceDecoder = EventJsonToScalaDslDecoders.eventInstanceDecoder

    def processIncomingMessage[A](rawMessage: String, decode: Json => Decoder.Result[A], process: A => Unit, failure: (String, String) => Unit): Unit = {
      parse(rawMessage).leftMap(_.message) match {
        case Left(jsonParseError) => failure(jsonParseError, rawMessage)
        case Right(json)          => decode(json).leftMap(_.message) match {
          case Left(errorMessage) => failure(rawMessage, errorMessage)
          case Right(event)       => process(event)
        }
      }
    }

    val consumerSettings = ConsumerSettings(
        keyDeserializer = Deserializer[IO, Option[String]],
        valueDeserializer = Deserializer[IO, String],
      )
        .withBootstrapServers(clientConfig.bootstrapServers)
        .withGroupId(clientConfig.group)
        .withAutoOffsetReset(AutoOffsetReset.Earliest)

    logger.info(s"Started listening $clientConfig")

    consumerStream(consumerSettings)
      .evalTap(_.subscribeTo(
        clientConfig.`recipe-events-topic`,
        clientConfig.`baker-events-topic`))
      .flatMap(_.stream)
      .map(committable => {
        val record = committable.record;
        val rawMessage = record.value
        record.topic match {
          case clientConfig.`baker-events-topic` =>
            processIncomingMessage(rawMessage, bakerEventsDecoder.decodeJson, eventProcessor.bakerEvent, eventProcessor.parseFailure)
          case clientConfig.`recipe-events-topic` =>
            processIncomingMessage(rawMessage, eventInstanceDecoder.decodeJson, eventProcessor.recipeEvent, eventProcessor.parseFailure)
          case _ =>
            logger.warn(s"Don't know how to process events from topic ${record.topic}")
        }
        committable.offset})
      .through(commitBatchWithin(1, 1.second)(IO.ioConcurrentEffect, timer))
      .compile
      .drain
      .as(ExitCode.Success)
  }

}