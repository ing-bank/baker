package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.{defaultinteractions, model, scaladsl}
import java.util.concurrent.ConcurrentHashMap

import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._

object CachedInteractionManager {

  def apply() = new CachedInteractionManager(List.empty)

  def apply(interactionInstance: scaladsl.InteractionInstance)(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(List(fromFuture(interactionInstance)))

  def apply(interactionInstance: scaladsl.InteractionInstance, allowSupersetForOutputTypes: Boolean)(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(List(fromFuture(interactionInstance)), allowSupersetForOutputTypes: Boolean)

  def apply(interactionInstances: List[scaladsl.InteractionInstance])(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactionInstances.map(fromFuture))

  def apply(interactionInstances: List[scaladsl.InteractionInstance], allowSupersetForOutputTypes: Boolean)(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactionInstances.map(fromFuture), allowSupersetForOutputTypes)

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

  def apply(interactionInstance: model.InteractionInstance[IO], allowSupersetForOutputTypes: Boolean) =
    new CachedInteractionManager(List(interactionInstance), allowSupersetForOutputTypes)

  def apply(interactionInstances: List[model.InteractionInstance[IO]]) =
    new CachedInteractionManager(interactionInstances)

 def apply(interactionInstances: List[model.InteractionInstance[IO]], allowSupersetForOutputTypes: Boolean) =
    new CachedInteractionManager(interactionInstances, allowSupersetForOutputTypes)

  def fromJava(interactions: java.util.List[AnyRef])(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)}.toList
    )

  def fromJava(interactions: java.util.List[AnyRef], allowSupersetForOutputTypes: Boolean)(implicit cs: ContextShift[IO]) =
    new CachedInteractionManager(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)}.toList
    ,allowSupersetForOutputTypes)

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
  *
  * @param availableImplementations    All the implemntations to be managed by this InteractionManager
  * @param allowSupersetForOutputTypes If this is set to true it will also allow fur supersets of the output types to be given by the implementations
  *                                    This can be helpful in case an ENUM type or similar is extended upon and you know these new values will not be given.
  *                                    If this new value is given from the implementation this will result in te runtime error and a technical failure of the interaction.
  */
class CachedInteractionManager(val availableImplementations: List[model.InteractionInstance[IO]],
                               override val allowSupersetForOutputTypes: Boolean = false) extends InteractionManager[IO] with CachingTransitionLookups {

  val allInteractions: List[InteractionInstance[IO]] = availableImplementations ++ defaultinteractions.getDefaultInteractions

  override def listAll: IO[List[model.InteractionInstance[IO]]] = IO(allInteractions)

  def combine(other: CachedInteractionManager): IO[CachedInteractionManager] = for {
    otherImplementations <- other.listAll
    theseImplementations <- listAll
  } yield CachedInteractionManager(theseImplementations ++ otherImplementations, allowSupersetForOutputTypes)
}

