package com.ing.baker.runtime.akka.actor

import akka.actor.ActorSystem
import akka.testkit.TestKit
import org.scalatest.BeforeAndAfterAll
import org.scalatest.wordspec.AnyWordSpecLike
import org.scalatest.matchers.should.Matchers

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._

class UtilSpec extends TestKit(ActorSystem("UtilSpec"))
  with AnyWordSpecLike
  with Matchers
  with BeforeAndAfterAll {

  override def afterAll(): Unit = {
    super.afterAll()
    shutdown(system)
  }

  implicit def ec: ExecutionContext = system.dispatcher

  "The Util class" should {

    "collect future results within specified timeout" in {

      val fastFutures = (1 to 5).map(_ => Future { Thread.sleep(100); true } )
      val slowFuture = Future { Thread.sleep(5000); false }

      val futures = fastFutures :+ slowFuture

      val collected = Util.collectFuturesWithin(futures, 1.second, system.scheduler)

      val expectedResult = List.fill(5)(true)

      collected shouldBe expectedResult
    }
  }
}
