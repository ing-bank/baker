package com.ing.baker.runtime.javadsl

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture

import cats.effect.{ContextShift, IO}
import cats.~>
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.scaladsl.InteractionInstanceF
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Type

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.compat.java8.FutureConverters._
import scala.concurrent.Future

abstract class InteractionInstance extends common.InteractionInstance[CompletableFuture] with JavaApi {

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override val name: String

  override val input: util.List[Type]

  override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()

  override def execute(input: util.List[IngredientInstance]): CompletableFuture[Optional[EventInstance]]

  private def wrapExecuteToFuture(input: Seq[scaladsl.IngredientInstance]): Future[Option[scaladsl.EventInstance]] = {
    FutureConverters.toScala(execute(input.map(_.asJava).asJava)
      .thenApply[Option[scaladsl.EventInstance]] {
        optional =>
          if (optional.isPresent) Some(optional.get().asScala)
          else None
      })
  }

  private def outputOrNone = {
    if (output.isPresent) Some(output.get.asScala.toMap.mapValues(_.asScala.toMap)) else None
  }

  def asScala: scaladsl.InteractionInstance = {
    scaladsl.InteractionInstance(
      name,
      input.asScala,
      input => wrapExecuteToFuture(input),
      outputOrNone
    )
  }

  def asEffectful(implicit cs: ContextShift[IO]): InteractionInstanceF[IO] = {
    InteractionInstanceF.build(
      name,
      input.asScala,
      input => IO.fromFuture(IO(wrapExecuteToFuture(input)))(cs),
      outputOrNone
    )
  }

}

object InteractionInstance {

  def fromList(implementations: java.util.List[AnyRef]): java.util.List[InteractionInstance] = {
    implementations.asScala.map(from).asJava
  }

  def from(implementation: AnyRef): InteractionInstance = {
    InteractionInstanceF.unsafeFrom[IO](implementation)
      .asJava(new (IO ~> CompletableFuture) {
        def apply[A](fa: IO[A]): CompletableFuture[A] = fa.unsafeToFuture().toJava.toCompletableFuture
      })
  }
}
