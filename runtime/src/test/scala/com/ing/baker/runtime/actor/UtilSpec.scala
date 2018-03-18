package com.ing.baker.runtime.actor

import scala.collection.immutable.List
import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration._
import org.scalatest.Matchers._

class UtilSpec extends AkkaTestBase {

  implicit def ec: ExecutionContext = system.dispatcher

  "The Util class" should {

    "collect future results within specified timeout" in {

      val nrOfResults = 10

      val f1 = (1 to nrOfResults).map(_ => Future { Thread.sleep(500); true } ).toList
      val f2 = (1 to nrOfResults).map(_ => Future { Thread.sleep(2500); false } ).toList

      val futures = f1 ++ f2

      val collected = Util.collectFuturesWithin(futures, 1 second, system.scheduler)

      val expectedResult = List.fill(nrOfResults)(true)

      collected shouldBe expectedResult
    }
  }
}
