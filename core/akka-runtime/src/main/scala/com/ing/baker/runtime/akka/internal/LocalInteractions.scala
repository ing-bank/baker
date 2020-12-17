package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionsF
import com.ing.baker.runtime.scaladsl.{InteractionInstance, InteractionInstanceF}

import java.util.concurrent.ConcurrentHashMap
import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._

object LocalInteractions {

  def apply() = new LocalInteractions(List.empty)

  def apply(interactionInstance: InteractionInstance)(implicit cs: ContextShift[IO]) =
    new LocalInteractions(List(fromFuture(interactionInstance)))

  def apply(interactionInstances: List[InteractionInstance])(implicit cs: ContextShift[IO]) =
    new LocalInteractions(interactionInstances.map(fromFuture))

  private def fromFuture(i: InteractionInstance)(implicit cs: ContextShift[IO]): InteractionInstanceF[IO] = {
    InteractionInstanceF.build(
      _name = i.name,
      _input = i.input,
      _run = p => IO.fromFuture(IO(i.run(p))),
      _output = i.output
    )
  }

  def apply(interactionInstance: InteractionInstanceF[IO]) =
    new LocalInteractions(List(interactionInstance))

  def apply(interactionInstances: List[InteractionInstanceF[IO]]) =
    new LocalInteractions(interactionInstances)

  def fromJava(interactions: java.util.List[AnyRef])(implicit cs: ContextShift[IO]) =
    new LocalInteractions(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => InteractionInstanceF.unsafeFrom[IO](other)
      }     .toList
    )

}

trait CachingTransitionLookups {
  self: InteractionsF[IO] =>

  type TransitionStorage = ConcurrentHashMap[InteractionTransition, InteractionInstanceF[IO]]

  private val transitionToInteractionCache: IO[Ref[IO, TransitionStorage]] =
    Ref.of[IO, TransitionStorage](new TransitionStorage)

  protected def findCompatible(instances: List[InteractionInstanceF[IO]], interaction: InteractionTransition): InteractionInstanceF[IO] =
    instances.find(implementation => compatible(interaction, implementation)).orNull

  override def findImplementation(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[InteractionInstanceF[IO]]] =
    for {
      cacheRef <- transitionToInteractionCache
      cache <- cacheRef.get
      instances <- self.availableInstances
    } yield Option(cache.computeIfAbsent(transition, (findCompatible (instances, _)).asJava))
}

/** The LocalInteractions class is responsible for all implementation of interactions.
  * It knows all implementations available locally, and gives the correct implementation for an interaction.
  * The set of interactions is immutable and interactions known for
  */
class LocalInteractions(val availableImplementations: List[InteractionInstanceF[IO]]) extends InteractionsF[IO] with CachingTransitionLookups {

  override def availableInstances: IO[List[InteractionInstanceF[IO]]] = IO(availableImplementations)

  def combine(other: LocalInteractions): IO[LocalInteractions] = for {
    otherImplementations <- other.availableInstances
    theseImplementations <- availableInstances
  } yield LocalInteractions(theseImplementations ++ otherImplementations)

}

