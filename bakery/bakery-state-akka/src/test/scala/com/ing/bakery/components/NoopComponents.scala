package com.ing.bakery.components

import cats.effect.IO
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
object NoopComponents {
  object TestInteractionManager extends InteractionManager[IO] {
    override def listAll: IO[List[InteractionInstance[IO]]] = IO.pure(List.empty)
  }
}
