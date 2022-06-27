package com.ing.baker.runtime.scaladsl

import cats.arrow.FunctionK
import com.ing.baker.runtime.model
import com.ing.baker.types.Type

import scala.collection.immutable.Seq
import scala.concurrent.{ExecutionContext, Future}

case class InteractionInstance(name: String,
                               input: Seq[InteractionInstanceInput],
                               run: Seq[IngredientInstance] => Future[Option[EventInstance]],
                               output: Option[Map[String, Map[String, Type]]] = None
                              ) extends model.InteractionInstanceF[Future]

object InteractionInstance {

  def fromFutureF(interactionInstance: model.InteractionInstanceF[Future]): InteractionInstance =
    interactionInstance.asDeprecatedFutureImplementation(FunctionK.id)

  def unsafeFromList(implementations: List[AnyRef])(implicit ec: ExecutionContext): List[InteractionInstance] = {
    implementations.map(unsafeFrom(_))
  }

  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionInstance = {
    fromFutureF(model.InteractionInstanceF.unsafeFrom[Future](implementation))
  }
}
