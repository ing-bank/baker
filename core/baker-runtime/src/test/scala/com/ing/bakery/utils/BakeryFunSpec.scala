package com.ing.bakery.utils

import cats.effect.unsafe.implicits.global
import cats.effect.{IO, Resource, Sync}
import org.scalatest.compatible.Assertion
import org.scalatest.funspec.FixtureAsyncFunSpecLike
import org.scalatest.{ConfigMap, FutureOutcome, Tag}

import scala.concurrent.duration._

/** Abstracts the common test practices across the Bakery project. */
abstract class BakeryFunSpec extends FixtureAsyncFunSpecLike {

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext

  /** Represents external arguments to the test context builder. */
  type TestArguments

  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext]

  def argumentsBuilder(config: ConfigMap): TestArguments

  /** Runs a single test with a clean sealed context. */
  def test(specText: String, testTags: Tag*)(runTest: TestContext => IO[Assertion]): Unit = {
      it(specText, testTags: _*)(args => {
        val temp1: Resource[IO, TestContext] = contextBuilder(args)
        temp1.use((context: TestContext) => {
          runTest(context)
        }).unsafeToFuture()
      })
  }

  /** Tries every second f until it succeeds or until 20 attempts have been made. */
  def eventually[A](f: IO[A])(implicit effect: Sync[IO]): IO[A] =
    within(20.seconds, 20)(f)

  /** Retries the argument f until it succeeds or time/split attempts have been made,
    * there exists a delay of time for each retry.
    */
  def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit sync: Sync[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => {
//          IO.sleep(times) *> inner(count - 1, times)
          IO.sleep(times).unsafeRunSync()
          inner(count - 1, times)
        }
        case Right(a: A) => sync.pure(a)
      }
    }
    inner(split, time / split)
  }

  override type FixtureParam = TestArguments

  override def withFixture(test: OneArgAsyncTest): FutureOutcome =
    test.apply(argumentsBuilder(test.configMap))
}
