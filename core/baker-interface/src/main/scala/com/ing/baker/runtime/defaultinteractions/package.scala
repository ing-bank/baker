package com.ing.baker.runtime

import com.ing.baker.runtime.catseffect.{AsyncSupport, EffectSupport}
import com.ing.baker.runtime.model.InteractionInstance
import com.typesafe.config.ConfigFactory

import scala.reflect.ClassTag

package object defaultinteractions {
  def all[F[_]](implicit async: AsyncSupport[F], classTag: ClassTag[F[Any]]): List[InteractionInstance[F]] = {
    implicit val effect: EffectSupport[F] = EffectSupport.fromApplicative[F](async.asyncInstance)

    val path = "baker.default-interactions.timer.skip"
    val config = ConfigFactory.load()
    val skipWait = config.hasPath(path) && config.getBoolean(path)
    List(
      InteractionInstance.unsafeFrom[F](new TimerInteraction[F](skipWait)),
      InteractionInstance.unsafeFrom[F](new TimerInteractionJava[F](skipWait)))
  }
}
