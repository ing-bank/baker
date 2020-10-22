package com.ing.baker.runtime.inmemory

import cats.effect.IO
import cats.effect.concurrent.Ref
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionInstanceManager
import com.ing.baker.runtime.scaladsl.InteractionInstance

object InMemoryInteractionInstanceManager {

  type Store = Set[InteractionInstance]

  def build: IO[InMemoryInteractionInstanceManager] =
    Ref.of[IO, Store](Set.empty).map(new InMemoryInteractionInstanceManager(_))
}

final class InMemoryInteractionInstanceManager(store: Ref[IO, InMemoryInteractionInstanceManager.Store]) extends InteractionInstanceManager[IO] {

  override def add(interaction: InteractionInstance): IO[Unit] =
    store.update(_ + interaction)

  override def get(interaction: InteractionTransition): IO[Option[InteractionInstance]] =
    store.get.map(_.find(isCompatible(interaction, _)))
}
