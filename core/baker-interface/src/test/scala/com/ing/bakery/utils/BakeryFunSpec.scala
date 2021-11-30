package com.ing.bakery.utils

import cats.implicits._
import cats.effect.{Effect, IO, Resource, Sync}
import org.scalactic.source
import org.scalatest.compatible.Assertion
import org.scalatest.funspec.FixtureAsyncFunSpecLike
import org.scalatest.{ConfigMap, FutureOutcome, Tag}

import scala.concurrent.duration._
import cats.effect.Temporal

/** Abstracts the common test practices across the Bakery project. */
abstract class BakeryFunSpec[F[_]] extends FixtureAsyncFunSpecLike {

  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(concurrent.ExecutionContext.global)

  implicit val timer: Temporal[IO] =
    IO.timer(concurrent.ExecutionContext.global)

  /** Represents the "sealed resources context" that each test can use. */
  type TestContext

  /** Represents external arguments to the test context builder. */
  type TestArguments

  /** Creates a `Resource` which allocates and liberates the expensive resources each test can use.
    * For example web servers, network connection, database mocks.
    *
    * The objective of this function is to provide "sealed resources context" to each test, that means context
    * that other tests simply cannot touch.
    *
    * @param testArguments arguments built by the `argumentsBuilder` function.
    * @return the resources each test can use
    */
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext]

  /** Refines the `ConfigMap` populated with the -Dkey=value arguments coming from the "sbt testOnly" command.
    *
    * @param config map populated with the -Dkey=value arguments.
    * @return the data structure used by the `contextBuilder` function.
    */
  def argumentsBuilder(config: ConfigMap): TestArguments

  /** Runs a single test with a clean sealed context. */
  def test(specText: String, testTags: Tag*)(runTest: TestContext => F[Assertion])(implicit pos: source.Position, effect: Effect[F]): Unit =
    it(specText, testTags: _*)(args =>
      contextBuilder(args).use(context => effect.toIO(runTest(context))).unsafeToFuture())

  /** Tries every second f until it succeeds or until 20 attempts have been made. */
  def eventually[A](f: F[A])(implicit effect: Sync[F], timer: Temporal[F]): F[A] =
    within(20.seconds, 20)(f)

  /** Retries the argument f until it succeeds or time/split attempts have been made,
    * there exists a delay of time for each retry.
    */
  def within[A](time: FiniteDuration, split: Int)(f: F[A])(implicit effect: Sync[F], timer: Temporal[F]): F[A] = {
    def inner(count: Int, times: FiniteDuration): F[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => timer.sleep(times) *> inner(count - 1, times)
        case Right(a) => effect.pure(a)
      }
    }

    inner(split, time / split)
  }

  override type FixtureParam = TestArguments

  override def withFixture(test: OneArgAsyncTest): FutureOutcome =
    test.apply(argumentsBuilder(test.configMap))
}