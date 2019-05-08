package com.ing.baker.runtime.core.actor

import scala.collection.immutable.List
import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._
import org.scalatest.Matchers._

class UtilSpec extends AkkaTestBase("UtilSpec") {

  implicit def ec: ExecutionContext = system.dispatcher

  "The Util class" should {

    "collect future results within specified timeout" in {

      val fastFutures = (1 to 5).map(_ => Future { Thread.sleep(100); true } )
      val slowFuture = Future { Thread.sleep(5000); false }

      val futures = fastFutures :+ slowFuture

      val collected = Util.collectFuturesWithin(futures, 1 second, system.scheduler)

      val expectedResult = List.fill(5)(true)

      collected shouldBe expectedResult
    }
  }
}
