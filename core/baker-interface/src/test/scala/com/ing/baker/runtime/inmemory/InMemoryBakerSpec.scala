package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.{BakerF, BakerModelSpec}
import com.ing.baker.runtime.scaladsl
import com.ing.baker.runtime.scaladsl.InteractionInstanceF

import scala.concurrent.duration._

class InMemoryBakerSpec extends BakerModelSpec[IO] {

  /** This will execute the predefined baker tests from BakerModelSpec */
  runAll()

  override def contextBuilder(testArguments: Unit): Resource[IO, Context] =
    for {
      _ <- Resource.liftF(IO.unit)
      _ = InMemoryBaker.java() // for coverage
    } yield Context((interactions: List[scaladsl.InteractionInstanceF[IO]]) => InMemoryBaker.build(BakerF.Config(
      bakeTimeout = 10.seconds,
      processEventTimeout = 10.seconds,
      inquireTimeout = 10.seconds,
      shutdownTimeout = 10.seconds,
      addRecipeTimeout = 10.seconds
    ), interactions))


}
