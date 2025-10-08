package com.ing.baker.runtime.inmemory

import cats.effect.unsafe.implicits.global
import cats.effect.{IO, Ref}
import cats.syntax.all._
import com.google.common.cache.{CacheBuilder, CacheLoader}
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus.Active
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.{BakerComponents, RecipeInstanceManager}
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata

import java.util.concurrent.ConcurrentMap
import scala.annotation.nowarn
import scala.concurrent.duration.FiniteDuration
import scala.jdk.CollectionConverters._

object InMemoryRecipeInstanceManager {

  type Store = ConcurrentMap[String, RecipeInstanceStatus[IO]]

  def build(idleTimeOut: FiniteDuration, retentionPeriodCheckInterval: FiniteDuration): IO[InMemoryRecipeInstanceManager] = {
    val cache: ConcurrentMap[String, RecipeInstanceStatus[IO]] = CacheBuilder.newBuilder()
      .build(new CacheLoader[String, RecipeInstanceStatus[IO]] {
        override def load(key: String): RecipeInstanceStatus[IO] = throw NoSuchProcessException("key")
      }).asMap()
    Ref.of[IO, Store](cache).map(new InMemoryRecipeInstanceManager(_, retentionPeriodCheckInterval, idleTimeOut))
  }
}

final class InMemoryRecipeInstanceManager(inmem: Ref[IO, InMemoryRecipeInstanceManager.Store],
                                          retentionPeriodCheckInterval: FiniteDuration,
                                          idleTimeOut: FiniteDuration) extends RecipeInstanceManager[IO] {

  //  We use this function instead of the startRetentionPeriodStream stream since it performs better
  def repeat(io : IO[Unit]) : IO[Nothing] = io >> IO.sleep(retentionPeriodCheckInterval) >> repeat(io)

  repeat(cleanupRecipeInstances(idleTimeOut)).unsafeRunAndForget()

  override def fetch(recipeInstanceId: String): IO[Option[RecipeInstanceStatus[IO]]] = {
    inmem.getAndUpdate(store => {
      Option.apply(store.get(recipeInstanceId)) match {
        case Some(recipeInstance: Active[IO]) =>
          store.put(recipeInstanceId, recipeInstance.copy(lastModified = System.currentTimeMillis()))
          store
        case _ => store
      }
    }).map(store => Option.apply(store.get(recipeInstanceId))
    )
  }

  override def store(newRecipeInstance: RecipeInstance[IO])(implicit components: BakerComponents[IO]): IO[Unit] =
    inmem.update(store => {
      store.put(newRecipeInstance.recipeInstanceId, RecipeInstanceStatus.Active(newRecipeInstance, System.currentTimeMillis()))
      store
    })

  override def idleStop(recipeInstanceId: String): IO[Unit] =
    IO.unit

  @nowarn
  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    inmem.get.flatMap(_.asScala.toMap.toList.traverse {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance, _)) =>
        recipeInstance.state.get.map(currentState => RecipeInstanceMetadata(currentState.recipe.recipeId, recipeInstanceId, currentState.createdOn))
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        IO.pure(RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn))
    }).map(_.toSet)

  @nowarn
  override protected def fetchAll: IO[Map[String, RecipeInstanceStatus[IO]]] =
    inmem.get.map(_.asScala.toMap)

  override def remove(recipeInstanceId: String): IO[Unit] =
    idleStop(recipeInstanceId) *>
      inmem.update(store => {
        store.remove(recipeInstanceId)
        store
      })
}
