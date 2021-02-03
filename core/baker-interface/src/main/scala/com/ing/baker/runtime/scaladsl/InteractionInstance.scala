package com.ing.baker.runtime.scaladsl

import cats.arrow.FunctionK
import com.ing.baker.types.Type

import scala.concurrent.{ExecutionContext, Future}

case class InteractionInstance( name: String,
                                input: Seq[Type],
                                run: Seq[IngredientInstance] => Future[Option[EventInstance]],
                                output: Option[Map[String, Map[String, Type]]] = None
                              ) extends InteractionInstanceF[Future]

object InteractionInstance {

  def fromFutureF(interactionInstanceF: InteractionInstanceF[Future]): InteractionInstance =
    interactionInstanceF.asDeprecatedFutureImplementation(FunctionK.id)

  def unsafeFromList(implementations: List[AnyRef])(implicit ec: ExecutionContext): List[InteractionInstance] = {
    implementations.map(unsafeFrom(_))
  }

  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionInstance = {
    fromFutureF(InteractionInstanceF.unsafeFrom[Future](implementation))
  }
}
