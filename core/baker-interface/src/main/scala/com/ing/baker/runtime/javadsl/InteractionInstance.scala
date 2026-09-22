package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, javadsl, model, scaladsl}
import com.ing.baker.types.Type

import java.util
import java.util.Optional
import java.util.concurrent.CompletableFuture
import scala.annotation.nowarn
import scala.concurrent.Future
import scala.concurrent.ExecutionContext.Implicits.global
import scala.jdk.CollectionConverters._
import scala.jdk.FutureConverters.FutureOps

abstract class InteractionInstance extends common.InteractionInstance[CompletableFuture] with JavaApi {

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override type Input = InteractionInstanceInput

  override val name: String

  override val input: util.List[InteractionInstanceInput]

  override val output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty()

  def run(input: util.List[IngredientInstance]): CompletableFuture[Optional[EventInstance]]

  override def execute(input: language.Seq[Ingredient], metaData: scala.collection.immutable.Map[String, String]): CompletableFuture[language.Option[Event]]

  private def wrapRunToFuture(input: Seq[scaladsl.IngredientInstance]): Future[Option[scaladsl.EventInstance]] = {
    import scala.concurrent.ExecutionContext.Implicits.global
    import scala.jdk.FutureConverters._
    run(input.map(_.asJava).asJava).asScala.map {
      optional =>
        if (optional.isPresent) Some(optional.get().asScala)
        else None
    }
  }

  private def outputOrNone: Option[Map[String, Map[String, Type]]] = {
    if (output.isPresent) Some(output.get.asScala.view.map { case (key, value) => (key, value.asScala.toMap)}.toMap) else None
  }

  def asScala: scaladsl.InteractionInstance = {
    scaladsl.InteractionInstance(
      name,
      input.asScala.map(input => input.asScala).toIndexedSeq,
      input => wrapRunToFuture(input),
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
    fromModel(model.InteractionInstance.unsafeFrom[Future](implementation))
  }

  private def fromModel(common: model.InteractionInstance[Future]): InteractionInstance = {
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

      override def run(input: util.List[javadsl.IngredientInstance]): CompletableFuture[Optional[javadsl.EventInstance]] =
        common.run(input.asScala.map(_.asScala).toIndexedSeq)
          .asJava
          .toCompletableFuture
          .thenApply(
            _.fold(Optional.empty[javadsl.EventInstance]())(
              e => Optional.of(e.asJava)))

      override def execute(input: language.Seq[Ingredient], metaData: scala.collection.immutable.Map[String, String]): CompletableFuture[language.Option[Event]] =
        run(input)
    }
  }
}
