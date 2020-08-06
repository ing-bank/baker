package com.ing.baker.baas.utils

import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.syntax.apply._
import org.scalactic.source
import org.scalatest.compatible.Assertion
import org.scalatest.funspec.FixtureAsyncFunSpecLike
import org.scalatest.{ConfigMap, FutureOutcome, Tag}

import scala.concurrent.duration._

/** Abstracts the common test practices across the Bakery project. */
abstract class BakeryFunSpec extends FixtureAsyncFunSpecLike {

  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(executionContext)

  implicit val timer: Timer[IO] =
    IO.timer(executionContext)

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
  def test(specText: String, testTags: Tag*)(runTest: TestContext => IO[Assertion])(implicit pos: source.Position): Unit =
    it(specText, testTags: _*)(args =>
      contextBuilder(args).use(runTest).unsafeToFuture())

  /** Tries every second f until it succeeds or until 20 attempts have been made. */
  def eventually[A](f: IO[A]): IO[A] =
    within(20.seconds, 20)(f)

  /** Retries the argument f until it succeeds or time/split attempts have been made,
    * there exists a delay of time for each retry.
    */
  def within[A](time: FiniteDuration, split: Int)(f: IO[A]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

  override type FixtureParam = TestArguments

  override def withFixture(test: OneArgAsyncTest): FutureOutcome =
    test.apply(argumentsBuilder(test.configMap))
}