package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.{BakerF, BakerModelSpec, InteractionInstance}

import scala.concurrent.duration._

class InMemoryBakerSpec extends BakerModelSpec[IO] {

  /** This will execute the predefined baker tests from BakerModelSpec */
  runAll()

  override def contextBuilder(testArguments: Unit): Resource[IO, Context] =
    for {
      _ <- Resource.eval(IO.unit)
      baker = InMemoryBaker.java() // for coverage
      _ = baker.gracefulShutdown()
    } yield Context((interactions: List[InteractionInstance[IO]]) => InMemoryBaker.build(BakerF.Config(
      bakeTimeout = 10.seconds,
      processEventTimeout = 10.seconds,
      inquireTimeout = 10.seconds,
      shutdownTimeout = 10.seconds,
      addRecipeTimeout = 10.seconds
    ), interactions))


}
