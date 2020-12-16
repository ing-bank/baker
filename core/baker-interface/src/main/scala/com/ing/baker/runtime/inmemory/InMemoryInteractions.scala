package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.InteractionInstanceF

object InMemoryInteractions {

  def build(implementations: Seq[InteractionInstanceF[IO]]): IO[InMemoryInteractions] =
    IO(new InMemoryInteractions(implementations))
}

final class InMemoryInteractions(implementations: Seq[InteractionInstanceF[IO]]) extends InteractionsF[IO] {

  override def instances: IO[Seq[InteractionInstanceF[IO]]] = IO(implementations)

  override def findImplementation(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[InteractionInstanceF[IO]]] =
    IO {
      println(s"in find implementation ${transition.interactionName}")
      implementations.find(compatible(transition, _))
    }

}
