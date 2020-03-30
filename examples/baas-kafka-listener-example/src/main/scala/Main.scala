import cats.effect.{ExitCode, IO, IOApp}
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import fs2.kafka._
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import cats.implicits._

object Main extends IOApp with LazyLogging {

  case class KafkaListenerConfig(
    bootstrapServers: String,
    group: String,
    `recipe-events-topic`: String,
    `bakery-events-topic`: String
  )

  override def run(args: List[String]): IO[ExitCode] = {

    val clientConfig = ConfigFactory.load().getConfig("baas-kafka-listener").as[KafkaListenerConfig]

    val consumerSettings = ConsumerSettings(
        keyDeserializer = Deserializer[IO, Option[String]],
        valueDeserializer = Deserializer[IO, String],
      )
        .withBootstrapServers(clientConfig.bootstrapServers)
        .withGroupId(clientConfig.group)
        .withAutoOffsetReset(AutoOffsetReset.Earliest)

    def processRecord(record: ConsumerRecord[Option[String], String]): IO[Unit] =
      IO(
        logger.info(s"Received: ${ record.value }")
      )

    consumerStream(consumerSettings)
      .evalTap(_.subscribeTo(
        clientConfig.`recipe-events-topic`,
        clientConfig.`bakery-events-topic`))
      .flatMap(_.stream)
      .map(record => processRecord(record.record))
      .compile
      .drain
      .as(ExitCode.Success)
  }

}