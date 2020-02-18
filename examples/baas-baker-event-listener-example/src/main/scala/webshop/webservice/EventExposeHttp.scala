package webshop.webservice

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.common.{InteractionCompleted, InteractionFailed, InteractionStarted, RecipeInstanceCreated}
import com.ing.baker.runtime.scaladsl.{BakerEvent, EventReceived, EventRejected, RecipeAdded}
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router

class EventExposeHttp(store: EventStore[BakerEvent])(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def serialize(event: BakerEvent): String =
    event match {
      case _: EventReceived => "EventReceived"
      case _: EventRejected => "EventRejected"
      case _: InteractionFailed => "InteractionFailed"
      case _: InteractionStarted => "InteractionStarted"
      case _: InteractionCompleted => "InteractionCompleted"
      case _: RecipeInstanceCreated => "RecipeInstanceCreated"
      case _: RecipeAdded => "RecipeAdded"
    }

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] =
    Router("/api" -> HttpRoutes.of[IO] {

      case GET -> Root =>
        Ok("Ok")

      case GET -> Root / "events" =>
        for {
          snapshot <- store.snapshot
          serialized = snapshot.map(serialize).mkString(", ")
          response <- Ok(serialized)
        } yield response
    })
}
