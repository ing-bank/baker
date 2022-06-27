package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}

object InMemoryInteractionManager {

  def build(implementations: List[InteractionInstance[IO]]): IO[InMemoryInteractionManager] =
    IO(new InMemoryInteractionManager(implementations))
}

final class InMemoryInteractionManager(implementations: List[InteractionInstance[IO]]) extends InteractionManager[IO] {

  override val allowSupersetForOutputTypes: Boolean = false

  override def listAll: IO[List[InteractionInstance[IO]]] = IO(implementations)

}
