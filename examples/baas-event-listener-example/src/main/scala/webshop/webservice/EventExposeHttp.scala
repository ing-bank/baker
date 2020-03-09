package webshop.webservice

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.scaladsl.EventInstance
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.implicits._
import org.http4s.server.Router

class EventExposeHttp(store: EventStore[EventInstance])(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] =
    Router("/api" -> HttpRoutes.of[IO] {

      case GET -> Root =>
        Ok("Ok")

      case GET -> Root / "events" =>
        for {
          snapshot <- store.snapshot
          serialized = snapshot.map(_.name).mkString(", ")
          response <- Ok(serialized)
        } yield response
    })
}
