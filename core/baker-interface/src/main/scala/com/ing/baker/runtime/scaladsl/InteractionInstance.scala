package com.ing.baker.runtime.scaladsl

import cats.arrow.FunctionK
import cats.effect.IO
import cats.~>
import com.ing.baker.runtime.javadsl
import com.ing.baker.types.Type

import java.util.concurrent.CompletableFuture
import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, Future}

case class InteractionInstance( name: String,
                                input: Seq[Type],
                                run: Seq[IngredientInstance] => Future[Option[EventInstance]],
                                output: Option[Map[String, Map[String, Type]]] = None
                              ) extends InteractionInstanceF[Future] {

  def asJavaCompletableFuture: javadsl.InteractionInstance =
    asJava(new (Future ~> CompletableFuture) {
      override def apply[A](fa: Future[A]): CompletableFuture[A] =
        FutureConverters.toJava(fa).toCompletableFuture
    })
}

object InteractionInstance {

  def fromF(interactionInstanceF: InteractionInstanceF[Future]): InteractionInstance =
    interactionInstanceF.asDeprecatedFutureImplementation(FunctionK.id)

  def unsafeFromList(implementations: List[AnyRef])(implicit ec: ExecutionContext): List[InteractionInstance] = {
    implementations.map(unsafeFrom(_))
  }

  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionInstance = {
    fromF(InteractionInstanceF.unsafeFrom[Future](implementation))
  }
}
