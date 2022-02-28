package com.ing.baker.runtime.inmemory

import java.util.concurrent.{ConcurrentMap, TimeUnit}

import cats.effect.IO
import cats.implicits._
import com.google.common.cache.{CacheBuilder, CacheLoader}
import com.ing.baker.runtime.common.BakerException.NoSuchProcessException
import com.ing.baker.runtime.model.RecipeInstanceManager.RecipeInstanceStatus
import com.ing.baker.runtime.model.recipeinstance.RecipeInstance
import com.ing.baker.runtime.model.{BakerComponents, RecipeInstanceManager}
import com.ing.baker.runtime.scaladsl.RecipeInstanceMetadata
import scala.collection.JavaConverters._

import scala.concurrent.duration.Duration
import cats.effect.{ Ref, Temporal }

object InMemoryRecipeInstanceManager {

  type Store = ConcurrentMap[String, RecipeInstanceStatus[IO]]

  def build(instanceTTL: Duration)(implicit timer: Temporal[IO]): IO[InMemoryRecipeInstanceManager] = {
    val cache: ConcurrentMap[String, RecipeInstanceStatus[IO]] = CacheBuilder.newBuilder()
      .expireAfterWrite(instanceTTL.toMillis, TimeUnit.MILLISECONDS)
      .build(new CacheLoader[String, RecipeInstanceStatus[IO]] {
        override def load(key: String): RecipeInstanceStatus[IO] = throw NoSuchProcessException("key")
      }).asMap()
    Ref.of[IO, Store](cache).map(new InMemoryRecipeInstanceManager(_))
  }
}

final class InMemoryRecipeInstanceManager(inmem: Ref[IO, InMemoryRecipeInstanceManager.Store])(implicit timer: Temporal[IO]) extends RecipeInstanceManager[IO] {

  override def fetch(recipeInstanceId: String): IO[Option[RecipeInstanceStatus[IO]]] =
    inmem.get.map(store => Option.apply(store.get(recipeInstanceId)))

  override def store(newRecipeInstance: RecipeInstance[IO])(implicit components: BakerComponents[IO]): IO[Unit] =
    inmem.update(store => {
      store.put(newRecipeInstance.recipeInstanceId, RecipeInstanceStatus.Active(newRecipeInstance))
      store
    })

  override def idleStop(recipeInstanceId: String): IO[Unit] =
    IO.unit

  override def getAllRecipeInstancesMetadata: IO[Set[RecipeInstanceMetadata]] =
    inmem.get.flatMap(_.asScala.toMap.toList.traverse {
      case (recipeInstanceId, RecipeInstanceStatus.Active(recipeInstance)) =>
        recipeInstance.state.get.map(currentState => RecipeInstanceMetadata(currentState.recipe.recipeId, recipeInstanceId, currentState.createdOn))
      case (recipeInstanceId, RecipeInstanceStatus.Deleted(recipeId, createdOn, _)) =>
        IO.pure(RecipeInstanceMetadata(recipeId, recipeInstanceId, createdOn))
    }).map(_.toSet)

  override protected def fetchAll: IO[Map[String, RecipeInstanceStatus[IO]]] =
    inmem.get.map(_.asScala.toMap)

  override protected def remove(recipeInstanceId: String): IO[Unit] =
    inmem.update(store => {
      store.remove(recipeInstanceId)
      store
    })
}
