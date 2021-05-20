package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.model
import java.util.concurrent.ConcurrentHashMap

import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._

object CachedInteractionManager {

  def apply() = new CachedInteractionManager(List.empty)

  def apply(interactionInstance: scaladsl.InteractionInstance)(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(List(fromFuture(interactionInstance)))

  def apply(interactionInstances: List[scaladsl.InteractionInstance])(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactionInstances.map(fromFuture))

  private def fromFuture(i: scaladsl.InteractionInstance)(implicit cs: ContextShift[IO]): model.InteractionInstance[IO] = {
    model.InteractionInstance.build(
      _name = i.name,
      _input = i.input,
      _run = p => IO.fromFuture(IO(i.run(p))),
      _output = i.output
    )
  }

  def apply(interactionInstance: model.InteractionInstance[IO]) =
    new CachedInteractionManager(List(interactionInstance))

  def apply(interactionInstances: List[model.InteractionInstance[IO]]) =
    new CachedInteractionManager(interactionInstances)

  def fromJava(interactions: java.util.List[AnyRef])(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)
      }     .toList
    )

}

/** Caching of match of interaction to a transition  */
trait CachingTransitionLookups {
  self: InteractionManager[IO] =>

  type TransitionStorage = ConcurrentHashMap[InteractionTransition, model.InteractionInstance[IO]]

  private val transitionToInteractionCache: IO[Ref[IO, TransitionStorage]] =
    Ref.of[IO, TransitionStorage](new TransitionStorage)

  protected def findCompatible(instances: List[model.InteractionInstance[IO]], interaction: InteractionTransition): model.InteractionInstance[IO] =
    instances.find(implementation => compatible(interaction, implementation)).orNull

  override def findFor(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[model.InteractionInstance[IO]]] =
    for {
      cacheRef <- transitionToInteractionCache
      cache <- cacheRef.get
      instances <- self.listAll
    } yield Option(cache.computeIfAbsent(transition, (findCompatible (instances, _)).asJava))
}

/**
  * The CachedInteractionManager is a InteractionManagerF[IO] with an interaction cache to ensure findCompatible is not called every execution
  * @param availableImplementations
  */
class CachedInteractionManager(val availableImplementations: List[model.InteractionInstance[IO]]) extends InteractionManager[IO] with CachingTransitionLookups {

  override def listAll: IO[List[model.InteractionInstance[IO]]] = IO(availableImplementations)

  def combine(other: CachedInteractionManager): IO[CachedInteractionManager] = for {
    otherImplementations <- other.listAll
    theseImplementations <- listAll
  } yield CachedInteractionManager(theseImplementations ++ otherImplementations)

}

