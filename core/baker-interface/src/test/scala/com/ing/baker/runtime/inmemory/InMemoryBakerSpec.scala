package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.{BakerConfig, BakerModelSpec}

import scala.concurrent.duration._

class InMemoryBakerSpec extends BakerModelSpec[IO] {

  /** This will execute the predefined baker tests from BakerModelSpec */
  runAll()

  override def contextBuilder(testArguments: Unit): Resource[IO, Context] =
    for {
      _ <- Resource.liftF(IO.unit)
    } yield Context(InMemoryBaker.build(BakerConfig(
      bakeTimeout = 1.seconds,
      processEventTimeout = 1.seconds,
      inquireTimeout = 1.seconds,
      shutdownTimeout = 1.seconds,
      addRecipeTimeout = 1.seconds
    )))

}
