package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.InteractionInstanceF

object InMemoryInteractions {

  def build(implementations: List[InteractionInstanceF[IO]]): IO[InMemoryInteractions] =
    IO(new InMemoryInteractions(implementations))
}

final class InMemoryInteractions(implementations: List[InteractionInstanceF[IO]]) extends InteractionsF[IO] {

  override def listAll: IO[List[InteractionInstanceF[IO]]] = IO(implementations)

  override def findFor(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[InteractionInstanceF[IO]]] =
    IO(implementations.find(compatible(transition, _)))
}
