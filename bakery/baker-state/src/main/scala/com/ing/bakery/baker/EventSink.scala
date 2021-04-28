package com.ing.bakery.baker

import cakesolutions.kafka.KafkaProducer.Conf
import cakesolutions.kafka.{KafkaProducer, KafkaProducerRecord}
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._
import org.apache.kafka.common.serialization.StringSerializer

import scala.util.{Failure, Success, Try}

trait EventSink {
  def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit]
  def close(): Unit = ()
  def attach(baker: AkkaBaker)(implicit cs: ContextShift[IO]): IO[Unit] = {
    IO.fromFuture(IO{baker.registerBakerEventListener {
      event => fire(event).unsafeRunAsyncAndForget()
    }}).flatMap(_ =>
      IO.fromFuture(IO{baker.registerEventListener {
        (_, event) => fire(event).unsafeRunAsyncAndForget()
      }}))
  }
}

class KafkaEventSink(config: Config) extends EventSink with LazyLogging {

  case class EventRecord(name: String, recipeInstanceId: Option[String], data: String)

  private implicit val EventRecordEncoder: Encoder[EventRecord] = deriveEncoder[EventRecord]

  private val producer =
    KafkaProducer(Conf(new StringSerializer(), new StringSerializer(), config.getString("bootstrap-servers")))

  private val topic = config.getString("topic")

  private def recordOf(eventInstance: EventInstance): EventRecord =
    EventRecord(eventInstance.name, None, "")

  private def recordOf(bakerEvent: BakerEvent): EventRecord = bakerEvent match {
    case EventReceived(_, _, _, recipeInstanceId, _, event) =>
      EventRecord("EventReceived", Option(recipeInstanceId), event.name)
    case EventRejected(_, recipeInstanceId, _, event, _) =>
      EventRecord("EventRejected", Option(recipeInstanceId), event.name)
    case InteractionFailed(_, _, _, _, recipeInstanceId, interactionName, _, throwable, _) =>
      EventRecord("InteractionFailed", Option(recipeInstanceId), s"$interactionName: ${throwable.getMessage}")
    case InteractionStarted(_, _, _, recipeInstanceId, interactionName) =>
      EventRecord("InteractionStarted", Option(recipeInstanceId), interactionName)
    case InteractionCompleted(_, _, _, _, recipeInstanceId, interactionName, event) =>
      EventRecord("InteractionCompleted", Option(recipeInstanceId),  s"$interactionName: ${event.map(_.name).getOrElse("")}")
    case RecipeInstanceCreated(_, recipeId, _, recipeInstanceId) =>
      EventRecord("RecipeInstanceCreated", Option(recipeInstanceId), recipeId)
    case RecipeAdded(recipeName, _, _, _) =>
      EventRecord("RecipeAdded", None, recipeName)
  }

  override def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit] = (event match {
    case eventInstance: EventInstance => Some(recordOf(eventInstance))
    case bakerEvent: BakerEvent    => Some(recordOf(bakerEvent))
    case _                =>
      logger.warn(s"Don't know where to send event of class ${ event.getClass.getSimpleName }: $event")
      None
  }) map { record =>
    IO.fromFuture(IO {
      producer.send(KafkaProducerRecord[String, String](topic, None,
        record.asJson.dropNullValues.toString.replace('\n', ' ')))
    }).map(_ =>  () )
  } getOrElse IO.unit

  override def close(): Unit = producer.close()

}

object EventSink extends LazyLogging {

  private lazy val NoSink = IO {
    new EventSink {
      override def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit] = IO.unit
    }
  }

  def resource(settings: Config)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, EventSink] = {

    Resource.make({
      val providerClass = settings.getString("provider-class")
      if (providerClass.isEmpty) {
        logger.info("No provider class specified: Kafka event sink disabled")
        NoSink
      } else {
        Try(Class.forName(providerClass).getDeclaredConstructor(classOf[com.typesafe.config.Config]).newInstance(settings)) match {
          case Success(sink: EventSink) =>
            logger.info(s"Using sink implementation $providerClass")
            IO(sink)
          case Success(_) => {
            logger.warn(s"Sink provider class $providerClass must extend ${EventSink.getClass.getCanonicalName}")
            NoSink
          }
          case Failure(exception) =>
            logger.error("Error initialising Kafka sink", exception)
            NoSink
        }
      }
    })(sink => IO(sink.close()))
  }
}

