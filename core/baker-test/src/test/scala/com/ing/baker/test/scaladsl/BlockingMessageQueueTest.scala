package com.ing.baker.test.scaladsl

import java.util.concurrent.TimeUnit

import akka.actor.ActorSystem
import com.ing.baker.test.common.AsyncMessages
import org.scalatest.matchers.should.Matchers
import org.scalatest.flatspec.AnyFlatSpec

import scala.concurrent.duration._
import scala.concurrent.{duration, _}
import scala.language.postfixOps

class BlockingMessageQueueTest extends AnyFlatSpec with Matchers {

  private val timeout = 1 seconds

  private val actorSystem = ActorSystem()
  private val scheduler = actorSystem.scheduler
  implicit val executor: ExecutionContextExecutor = ActorSystem().dispatcher

  private def delay(runnable: => Any) =
    scheduler.scheduleOnce(duration.Duration(100, TimeUnit.MILLISECONDS))(runnable)

  private val msg1 = "bla"
  private val msg2 = "bla bla"

  private def isMsg1: Predicate[String] = msg => msg == msg1

  private def isMsg2: Predicate[String] = msg => msg == msg2

  "WaitingMessageQueue" should "work with one message added before" in {
    val queue = new AsyncMessages[String]
    queue.put(msg1)
    val msgs = Await.result(queue.get(isMsg1), timeout)
    assertResult(Set(msg1))(msgs)
  }

  "WaitingMessageQueue" should "work with one message added after" in {
    val queue = new AsyncMessages[String]
    delay {
      queue.put(msg1)
    }
    assertResult(false)(queue.contains(isMsg1))
    val msgs = Await.result(queue.get(isMsg1), timeout)
    assertResult(Set(msg1))(msgs)
  }

  "WaitingMessageQueue" should "work with multiple predicates" in {
    val queue = new AsyncMessages[String]
    queue.put(msg1)
    queue.put(msg2)

    assertResult(true)(queue.contains(isMsg1))
    assertResult(true)(queue.contains(isMsg2))

    val msgs = Await.result(queue.get(isMsg1, isMsg2), timeout)
    assertResult(Set(msg1, msg2))(msgs)
  }

  "WaitingMessageQueue" should "work with multiple predicates and delay" in {
    val queue = new AsyncMessages[String]

    delay {
      queue.put(msg1)
      queue.put(msg2)
    }

    assertResult(false)(queue.contains(isMsg1))
    assertResult(false)(queue.contains(isMsg2))

    val msgs = Await.result(queue.get(isMsg1, isMsg2), timeout)
    assertResult(Set(msg1, msg2))(msgs)
  }

  "WaitingMessageQueue" should "work with high load" in {
    val queue = new AsyncMessages[String]

    val msgs = (0 to 100).map(i => s"msg$i")
    delay {
      msgs.foreach(queue.put)
    }

    val predicates: Seq[String => Boolean] =
      msgs.map(msg => { m: String => m == msg })

    val result = Await.result(queue.get(predicates: _*), 5 seconds)
    assertResult(msgs.toSet)(result)
  }
}
