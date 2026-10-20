package com.ing.baker.runtime.akka

import akka.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtension}
import akka.testkit.TestProbe
import com.ing.baker._
import com.ing.baker.runtime.testkit.BakerInquireSpecLike

import scala.language.postfixOps

class BakerInquireSpec extends BakerAkkaRuntimeTestBase with BakerInquireSpecLike {

  override def actorSystemName = "BakerInquireSpec"

  before {
    resetMocks()
    setupMockResponse()

    // Clean inmemory-journal before each test
    val tp = TestProbe()
    tp.send(StorageExtension(defaultActorSystem).journalStorage, InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(akka.actor.Status.Success(""))
  }

}
