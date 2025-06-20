package com.ing.bakery.components

import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.AkkaBaker
import com.ing.baker.runtime.scaladsl._
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import io.circe._
import io.circe.generic.semiauto._
import io.circe.syntax._
import org.apache.kafka.clients.producer.{Callback, KafkaProducer, ProducerRecord, RecordMetadata}
import org.apache.kafka.common.serialization.StringSerializer

import java.util.Properties
import scala.concurrent.Promise
import scala.util.control.NonFatal
import scala.util.{Failure, Success, Try}

trait EventSink {
  def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit]
  def close(): Unit = ()
  def attach(baker: AkkaBaker)(implicit cs: ContextShift[IO]): IO[Unit] = {
    IO.fromFuture(IO{baker.registerBakerEventListener {
      event => fire(event).unsafeRunAsyncAndForget()
    }})
  }
}

class KafkaEventSink(config: Config) extends EventSink with LazyLogging {

  case class EventRecord(name: String, recipeInstanceId: Option[String], data: String)

  private implicit val EventRecordEncoder: Encoder[EventRecord] = deriveEncoder[EventRecord]

  private val producer = {
    val props = new Properties
    props.put("bootstrap.servers", config.getString("baker.event-sink.bootstrap-servers"))
    new KafkaProducer(
      props, new StringSerializer(), new StringSerializer(),
    )
  }

  private val topic = config.getString("baker.event-sink.topic")

  private def recordOf(eventInstance: EventInstance): EventRecord =
    EventRecord(eventInstance.name, None, "")

  private def recordOf(bakerEvent: BakerEvent): EventRecord = bakerEvent match {
    case EventReceived(_, _, _, recipeInstanceId, _, eventName) =>
      EventRecord("EventReceived", Option(recipeInstanceId), eventName)
    case EventRejected(_, recipeInstanceId, _, eventName, _) =>
      EventRecord("EventRejected", Option(recipeInstanceId), eventName)
    case InteractionFailed(_, _, _, _, recipeInstanceId, interactionName, _, errorMessage, _) =>
      EventRecord("InteractionFailed", Option(recipeInstanceId), s"$interactionName: $errorMessage")
    case InteractionStarted(_, _, _, recipeInstanceId, interactionName) =>
      EventRecord("InteractionStarted", Option(recipeInstanceId), interactionName)
    case InteractionCompleted(_, _, _, _, recipeInstanceId, interactionName, eventName) =>
      EventRecord("InteractionCompleted", Option(recipeInstanceId),  s"$interactionName: ${eventName.getOrElse("")}")
    case RecipeInstanceCreated(_, recipeId, _, recipeInstanceId) =>
      EventRecord("RecipeInstanceCreated", Option(recipeInstanceId), recipeId)
    case RecipeAdded(recipeName, _, _, _) =>
      EventRecord("RecipeAdded", None, recipeName)
    case EventFired(_, _, _, recipeInstanceId, eventName) =>
      EventRecord("EventFired", Some(recipeInstanceId), eventName)
  }

  private def producerCallback(promise: Promise[RecordMetadata]): Callback =
    producerCallback(result => promise.complete(result))

  private def producerCallback(callback: Try[RecordMetadata] => Unit): Callback =
    (metadata: RecordMetadata, exception: Exception) => {
      val result =
        if (exception == null) Success(metadata)
        else Failure(exception)
      callback(result)
    }

  override def fire(event: Any)(implicit cs: ContextShift[IO]): IO[Unit] = (event match {
    case eventInstance: EventInstance => Some(recordOf(eventInstance))
    case bakerEvent: BakerEvent    => Some(recordOf(bakerEvent))
    case _                =>
      logger.warn(s"Don't know where to send event of class ${ event.getClass.getSimpleName }: $event")
      None
  }) map { record =>
    IO.fromFuture(IO {
      val promise = Promise[RecordMetadata]()
      try {
        producer.send(new ProducerRecord[String, String](topic, null,
          record.asJson.dropNullValues.toString.replace('\n', ' ')),
          producerCallback(promise))
      } catch {
        case NonFatal(e) => promise.failure(e)
      }
      promise.future
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

  def resource(config: Config)(implicit contextShift: ContextShift[IO], timer: Timer[IO]): Resource[IO, EventSink] = {

    Resource.make({
      val providerClass = config.getString("baker.event-sink.class")
      if (providerClass.isEmpty) {
        logger.info("No class specified: Kafka event sink disabled")
        NoSink
      } else {
        Try(Class.forName(providerClass).getDeclaredConstructor(classOf[com.typesafe.config.Config]).newInstance(config)) match {
          case Success(sink: EventSink) =>
            logger.info(s"Using sink provider implementation $providerClass")
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

