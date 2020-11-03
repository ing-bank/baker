package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.BakerModelSpec

class InMemoryBakerSpec extends BakerModelSpec[IO] {

  /** This will execute the predefined baker tests from BakerModelSpec */
  runTests()

  override def contextBuilder(testArguments: Unit): Resource[IO, Context] =
    for {
      _ <- Resource.liftF(IO.unit)
    } yield Context(InMemoryBaker.build())

}
