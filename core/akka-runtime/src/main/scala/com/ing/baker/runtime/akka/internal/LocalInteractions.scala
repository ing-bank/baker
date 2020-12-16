package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Sync}
import cats.implicits._
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.{InteractionInstance, InteractionInstanceF}

import java.util.concurrent.ConcurrentHashMap
import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._

object LocalInteractions {

  def apply(interactionInstance: InteractionInstanceF[IO]) =
    new LocalInteractions(List(interactionInstance))

  def apply() = new LocalInteractions(List.empty)

  def apply(interactionInstances: List[InteractionInstance])(implicit cs: ContextShift[IO]) =
    new LocalInteractions(interactionInstances.map(i =>
      InteractionInstanceF.build(
        _name = i.name,
        _input = i.input,
        _run = p => IO.fromFuture(IO(i.run(p))),
        _output = i.output
      )
    ))

  def apply(interactionInstances: List[InteractionInstanceF[IO]]) =
    new LocalInteractions(interactionInstances)

  def apply(interactions: java.util.List[AnyRef]) =
    new LocalInteractions(interactions
        .asScala
        .map(t => InteractionInstanceF.unsafeFrom[IO](t)).toList
    )
}

/** The LocalInteractions class is responsible for all implementation of interactions.
  * It knows all implementations available locally, and gives the correct implementation for an interaction.
  * The set of interactions is immutable and interactions known for
  */
class LocalInteractions(val availableImplementations: List[InteractionInstanceF[IO]]) extends InteractionsF[IO]  {

  override def instances: IO[List[InteractionInstanceF[IO]]] = IO(availableImplementations)

  def combine(other: LocalInteractions): IO[LocalInteractions] = for {
    otherImplementations <- other.instances
    theseImplementations <- instances
  } yield LocalInteractions(theseImplementations ++ otherImplementations)

  private[internal] val transitionToInteractionCache: IO[Ref[IO, ConcurrentHashMap[InteractionTransition, InteractionInstanceF[IO]]]] =
    Ref.of[IO, ConcurrentHashMap[InteractionTransition, InteractionInstanceF[IO]]](new ConcurrentHashMap[InteractionTransition, InteractionInstanceF[IO]])

  private def find(instances: List[InteractionInstanceF[IO]], interaction: InteractionTransition): InteractionInstanceF[IO] =
    instances.find(implementation => compatible(interaction, implementation)).orNull

  override def findImplementation(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[InteractionInstanceF[IO]]] =

    for {
      cacheRef <- transitionToInteractionCache
      cache <- cacheRef.get
      instances <- instances
    } yield {
      Option(cache.computeIfAbsent(transition, (t => find (instances, t)).asJava))
    }


}

