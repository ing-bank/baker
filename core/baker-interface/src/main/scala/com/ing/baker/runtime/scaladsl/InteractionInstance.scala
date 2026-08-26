package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.FunctionK
import com.ing.baker.runtime.model
import com.ing.baker.types.Type

import scala.concurrent.{ExecutionContext, Future}

case class InteractionInstance(name: String,
                               input: Seq[InteractionInstanceInput],
                               run: Seq[IngredientInstance] => Future[Option[EventInstance]],
                               output: Option[Map[String, Map[String, Type]]] = None
                              ) extends model.InteractionInstance[Future]

object InteractionInstance {
  def unsafeFrom(implementation: AnyRef)(implicit ec: ExecutionContext): InteractionInstance = {
    model
      .InteractionInstance
      .unsafeFrom[Future](implementation)
      .asDeprecatedFutureImplementation(FunctionK.id)
  }
}
