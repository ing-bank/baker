package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.{defaultinteractions, model, scaladsl}

import java.util.concurrent.ConcurrentHashMap
import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._
import scala.concurrent.ExecutionContext

object CachingInteractionManager {

  private def create(interactionInstances: List[model.InteractionInstance[IO]], maybeAllowSupersetForOutputTypes: Option[Boolean] = None): CachingInteractionManager = {
    new CachingInteractionManager {
      override def listAll: IO[List[model.InteractionInstance[IO]]] = IO.pure(interactionInstances)

      override val allowSupersetForOutputTypes: Boolean =
        maybeAllowSupersetForOutputTypes.getOrElse(super.allowSupersetForOutputTypes)
    }
  }

  def apply(): CachingInteractionManager = create(List.empty)

  def apply(interactionInstance: scaladsl.InteractionInstance): CachingInteractionManager =
    create(List(fromFuture(interactionInstance)))

  def apply(interactionInstance: scaladsl.InteractionInstance, allowSupersetForOutputTypes: Boolean): CachingInteractionManager =
    create(List(fromFuture(interactionInstance)), Some(allowSupersetForOutputTypes))

  def apply(interactionInstances: List[scaladsl.InteractionInstance]): CachingInteractionManager =
    create(interactionInstances.map(fromFuture))

  def apply(interactionInstances: List[scaladsl.InteractionInstance], allowSupersetForOutputTypes: Boolean): CachingInteractionManager =
    create(interactionInstances.map(fromFuture),  Some(allowSupersetForOutputTypes))

  private def fromFuture(i: scaladsl.InteractionInstance): model.InteractionInstance[IO] = {
    implicit val executionContext: ExecutionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] =  IO.contextShift(executionContext)
    model.InteractionInstance.build(
      _name = i.name,
      _input = i.input,
      _run = p => IO.fromFuture(IO(i.run(p))),
      _output = i.output
    )
  }

  def apply(interactionInstance: model.InteractionInstance[IO]): CachingInteractionManager =
    create(List(interactionInstance))

  def apply(interactionInstance: model.InteractionInstance[IO], allowSupersetForOutputTypes: Boolean): CachingInteractionManager =
    create(List(interactionInstance), Some(allowSupersetForOutputTypes))

  def fromJava(interactions: java.util.List[AnyRef]): CachingInteractionManager =
    create(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)
      }.toList
    )

  def fromJava(interactions: java.util.List[AnyRef], allowSupersetForOutputTypes: Boolean = true): CachingInteractionManager =
    create(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)
      }.toList
      , Some(allowSupersetForOutputTypes))

}

/** Caching of match of interaction to a transition */
trait CachingTransitionLookups {
  self: InteractionManager[IO] =>

  type TransitionStorage = ConcurrentHashMap[InteractionTransition, model.InteractionInstance[IO]]

  private val transitionToInteractionCache: IO[Ref[IO, TransitionStorage]] =
    Ref.of[IO, TransitionStorage](new TransitionStorage)

  protected def findCompatible(instances: List[model.InteractionInstance[IO]], interaction: InteractionTransition): model.InteractionInstance[IO] =
    instances.find(implementation => compatible(interaction, implementation)).orNull

  protected def transitionCache: IO[TransitionStorage] = for {
    cacheRef <- transitionToInteractionCache
    cache <- cacheRef.get
  } yield cache

  protected def clearTransitionCache(): IO[Unit] = for {
    cache <- transitionCache
    _ = cache.clear()
  } yield ()

  override def findFor(transition: InteractionTransition)(implicit sync: Sync[IO]): IO[Option[model.InteractionInstance[IO]]] =
    for {
      cache <- transitionCache
      instances <- self.listAll
    } yield Option(cache.computeIfAbsent(transition, (findCompatible(instances, _)).asJava))
}

/**
  * The CachedInteractionManager is a InteractionManagerF[IO] with an interaction cache
  * to ensure findCompatible is not called every execution
  */
trait CachingInteractionManager extends InteractionManager[IO] with CachingTransitionLookups

/**
  * Interaction manager that runs some sort of discovery process.
  * Set of interactions may change over time.
  */
trait DynamicInteractionManager extends CachingInteractionManager {

  case class InteractionBundle(startedAt: Long, interactions: List[InteractionInstance[IO]])
  type DiscoveredInteractions = ConcurrentHashMap[String, InteractionBundle]

  def listAll: IO[List[InteractionInstance[IO]]] = for {
    d <- discovered
  } yield d.values().asScala.flatMap(_.interactions).toList

  private val discoveredInteractions: IO[Ref[IO, DiscoveredInteractions]] =
    Ref.of[IO, DiscoveredInteractions](new DiscoveredInteractions)

  protected def discovered: IO[DiscoveredInteractions] = for {
    discoveredRef <- discoveredInteractions
    discovered <- discoveredRef.get
  } yield discovered

  def resource: Resource[IO, DynamicInteractionManager]

}
