package com.ing.baker.runtime.inmemory

import cats.effect.{IO, Resource}
import com.ing.baker.runtime.model.{BakerConfig, BakerF, BakerModelSpec, InteractionInstance}

import scala.concurrent.duration._
import scala.jdk.DurationConverters._

class InMemoryBakerSpec extends BakerModelSpec {

  /** This will execute the predefined baker tests from BakerModelSpec */
  runAll()

  override def contextBuilder(testArguments: Unit): Resource[IO, Context] =
    for {
      _ <- Resource.eval(IO.unit)
      baker = InMemoryBaker.java() // for coverage
      _ = baker.gracefulShutdown()
    } yield Context((interactions: List[InteractionInstance[IO]]) => InMemoryBaker.build(
      BakerConfig.default().withInquireTimeout(10.seconds.toJava),
      interactions
    ).asInstanceOf[IO[BakerF[IO]]])
}
