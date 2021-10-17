package com.ing.baker.runtime.akka.internal

import cats.effect.concurrent.Ref
import cats.effect.{ContextShift, IO, Resource, Sync}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.model.{InteractionInstance, InteractionManager}
import com.ing.baker.runtime.{defaultinteractions, model, scaladsl}

import java.util.concurrent.ConcurrentHashMap
import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._
import scala.concurrent.ExecutionContext

object CachingInteractionManager {

  private def create(interactionInstances: List[model.InteractionInstance[IO]], maybeAllowSupersetForOutputTypes: Option[Boolean] = None): CachingInteractionManager = {
    new CachingInteractionManager {
      override def listAll: IO[List[model.InteractionInstance[IO]]] =
        IO.pure(interactionInstances  ++ defaultinteractions.all)

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
    create(List(interactionInstance),  Some(allowSupersetForOutputTypes))

  def fromJava(interactions: java.util.List[AnyRef]): CachingInteractionManager =
    create(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)}.toList
    )

  def fromJava(interactions: java.util.List[AnyRef], allowSupersetForOutputTypes: Boolean = true): CachingInteractionManager =
    create(interactions
      .asScala
      .map {
        case javaInteraction: com.ing.baker.runtime.javadsl.InteractionInstance => fromFuture(javaInteraction.asScala)
        case other => model.InteractionInstance.unsafeFrom[IO](other)}.toList
    , Some(allowSupersetForOutputTypes))

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
trait CachingInteractionManager extends InteractionManager[IO] with CachingTransitionLookups

trait DynamicInteractionManager extends CachingInteractionManager {

  type DiscoveredInteractions = ConcurrentHashMap[String, List[InteractionInstance[IO]]]

  def bundledIntreactions: List[InteractionInstance[IO]] = defaultinteractions.all

  def listAll: IO[List[InteractionInstance[IO]]] = for {
    d <- discovered
  } yield bundledIntreactions ++ d.values().asScala.flatten.toList

  private val discoveredInteractions: IO[Ref[IO, DiscoveredInteractions]] =
    Ref.of[IO, DiscoveredInteractions](new DiscoveredInteractions)

  protected def discovered: IO[DiscoveredInteractions] = for {
    discoveredRef <- discoveredInteractions
    discovered <- discoveredRef.get
  } yield discovered

  def resource: Resource[IO, DynamicInteractionManager]

}
