package com.ing.baker.runtime.javadsl

import cats.effect.IO
import cats.~>
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, javadsl, model, scaladsl}
import com.ing.baker.types.Type

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import scala.annotation.nowarn
import scala.collection.JavaConverters._
import scala.collection.immutable.Seq
import scala.compat.java8.FutureConverters
import scala.compat.java8.FutureConverters._
import scala.concurrent.Future


abstract class InteractionInstance extends common.InteractionInstance[CompletableFuture] with JavaApi {

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override type Input = InteractionInstanceInput

  override val name: String

  override val input: util.List[InteractionInstanceInput]

  override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()

  override def execute(input: util.List[IngredientInstance]): CompletableFuture[Optional[EventInstance]]

  @nowarn
  private def wrapExecuteToFuture(input: Seq[scaladsl.IngredientInstance]): Future[Option[scaladsl.EventInstance]] = {
    FutureConverters.toScala(execute(input.map(_.asJava).asJava)
      .thenApply[Option[scaladsl.EventInstance]] {
        optional =>
          if (optional.isPresent) Some(optional.get().asScala)
          else None
      })
  }

  @nowarn
  private def outputOrNone: Option[Map[String, Map[String, Type]]] = {
    if (output.isPresent) Some(output.get.asScala.view.map { case (key, value) => (key, value.asScala.toMap)}.toMap) else None
  }

  @nowarn
  def asScala: scaladsl.InteractionInstance = {
    scaladsl.InteractionInstance(
      name,
      input.asScala.map(input => input.asScala).toIndexedSeq,
      input => wrapExecuteToFuture(input),
      outputOrNone
    )
  }

  @nowarn
  def asEffectful: common.InteractionInstance[IO] = {
    model.InteractionInstance.build(
      name,
      input.asScala.map(input => input.asScala).toIndexedSeq,
      input => IO.fromFuture(IO(wrapExecuteToFuture(input)))(cs),
      outputOrNone
    )
  }
}

object InteractionInstance {

  @nowarn
  def fromList(implementations: java.util.List[AnyRef]): java.util.List[InteractionInstance] = {
    implementations.asScala.map(from).asJava
  }

  def from(implementation: AnyRef): InteractionInstance = {
    fromModel(model.InteractionInstance.unsafeFrom[IO](implementation))
  }

  @nowarn
  def fromModel(common: model.InteractionInstance[IO]): InteractionInstance = {
    val converter = new (IO ~> CompletableFuture) {
      def apply[A](fa: IO[A]): CompletableFuture[A] = fa.unsafeToFuture().toJava.toCompletableFuture
    }
    new javadsl.InteractionInstance {
      override val name: String =
        common.name
      override val input: util.List[javadsl.InteractionInstanceInput] =
        common.input.map(input => input.asJava).asJava
      override val output: Optional[util.Map[String, util.Map[String, Type]]] =
        common.output match {
          case Some(out) => Optional.of(out.view.map { case (key, value) => (key, value.asJava)}.toMap.asJava)
          case None => Optional.empty[util.Map[String, util.Map[String, Type]]]()
        }
      override def execute(input: util.List[javadsl.IngredientInstance]): CompletableFuture[Optional[javadsl.EventInstance]] =
        converter(common.run(input.asScala.map(_.asScala).toIndexedSeq))
          .thenApply(
            _.fold(Optional.empty[javadsl.EventInstance]())(
              e => Optional.of(e.asJava)))
    }
  }
}
