package webshop.webservice

import cats.effect.{ExitCode, IO, IOApp}
import cats.implicits._
import com.ing.baker.baas.scaladsl.RemoteBakerEventListener
import com.ing.baker.runtime.scaladsl.BakerEvent
import com.typesafe.scalalogging.LazyLogging
import org.http4s.server.blaze.BlazeServerBuilder
import webshop.webservice.EventStore.Enqueue

object Main extends IOApp with LazyLogging {

  def unsafeEnqueueWith(enqueue: Enqueue[BakerEvent])(event: BakerEvent): Unit = {
    logger.info(event.toString)
    enqueue(event).unsafeRunSync()
  }

  override def run(args: List[String]): IO[ExitCode] = for {
    port <- IO( System.getenv("EXPOSE_EVENTS_PORT").toInt )
    store <- EventStore.build[BakerEvent]
    _ <- IO(RemoteBakerEventListener.load(unsafeEnqueueWith(store._1)))
    service = new EventExposeHttp(store._2)
    exitCode <- BlazeServerBuilder[IO]
      .bindHttp(port, "0.0.0.0")
      .withHttpApp(service.build)
      .resource
      .use(_ => IO.never)
      .as(ExitCode.Success)
  } yield exitCode
}
