package com.ing.baker.runtime.inmemory

import cats.effect.IO
import com.ing.baker.runtime.model.{InteractionInstanceF, InteractionManager}

object InMemoryInteractionManager {

  def build(implementations: List[InteractionInstanceF[IO]]): IO[InMemoryInteractionManager] =
    IO(new InMemoryInteractionManager(implementations))
}

final class InMemoryInteractionManager(implementations: List[InteractionInstanceF[IO]]) extends InteractionManager[IO] {

  override val allowSupersetForOutputTypes: Boolean = false

  override def listAll: IO[List[InteractionInstanceF[IO]]] = IO(implementations)

}
