package com.ing.baker.runtime.model

import org.scalatest.FlatSpec

class AsyncModelTests extends FlatSpec {

  type Test[A] = AsyncModel[String, A]

  def eventA0: Test[Int] = AsyncModel.async(10)

  def eventA1: Test[Int] = AsyncModel.async(100)

  def eventAA: Test[Int] = eventA0.flatMap(_ => eventA1)

  def eventB: Test[Int] = AsyncModel.async(2).map(_ + 3)

  def eventC(x: Int, y: Int): Test[Int] = AsyncModel.async(x * y)

  "Simple Lamport Clocks" should "async count from 0" in {
    val (lamportClock, result) = eventA0.run
    assert(lamportClock == 1 && result == Right(10))
  }

  it should "sequential causality moves clock forward" in {
    val (lamportClock, result) = eventAA.run
    assert(lamportClock == 2 && result == Right(100))
  }

  it should "sequential causality moves clock forward 2" in {
    val (lamportClock0, _) = eventA1.flatMap(_ => eventAA).run
    val (lamportClock1, _) = eventAA.flatMap(_ => eventA1).run
    assert(lamportClock0 == 3)
    assert(lamportClock1 == 3)
  }

  it should "sequential causality moves clock forward 3" in {
    val program0 = for {
      _ <- eventA0
      _ <- eventA0
      _ <- eventA0
      _ <- eventA0
    } yield ()
    val program1 = for {
      _ <- eventA0
      _ <- eventA0
      _ <- eventA0
      _ <- eventA0
    } yield ()
    val (lamportClock, _) = program0.flatMap(_ => program1).run
    assert(lamportClock == 8)
  }

  it should "not count pure applications" in {
    val (lamportClock, result) = AsyncModel.ok(1).run
    assert(lamportClock == 0 && result == Right(1))
  }

  it should "not count pure applications 2" in {
    val (lamportClock, result) = eventB.run
    assert(lamportClock == 1 && result == Right(5))
  }

  it should "take the longest clock from a tuple" in {
    val (lamportClock, result) = AsyncModel.parallel(eventA0, eventAA).run
    assert(lamportClock == 2 && result == Right(10, 100))
  }

  it should "take the longest clock from a list" in {
    val (lamportClock, result) = AsyncModel.parallelAll(List(eventA0, eventAA)).run
    assert(lamportClock == 2 && result == Right(List(10, 100)))
  }

  "Simple parallel and sequential" should "tuples" in {
    val program: Test[Int] = for {
      xy <- AsyncModel.parallel(eventAA, eventB)
      z <- eventC(xy._1, xy._2)
    } yield z

    val (lamportClock, result) = program.run
    assert(lamportClock == 3 && result == Right(100 * (2 + 3)))
  }

  it should "list" in {
    val program: Test[Int] = for {
      xy <- AsyncModel.parallelAll(List(eventAA, eventB))
      z <- {
        xy match {
          case x :: y :: Nil => eventC(x, y)
          case _ => AsyncModel.asyncFail("Unexpected events")
        }
      }
    } yield z

    val (lamportClock, result) = program.run
    assert(lamportClock == 3 && result == Right(100 * (2 + 3)))
  }
}
