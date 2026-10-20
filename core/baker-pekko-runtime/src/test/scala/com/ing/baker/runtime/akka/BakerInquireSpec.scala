package com.ing.baker.runtime.akka

import com.ing.baker._
import com.ing.baker.runtime.testkit.BakerInquireSpecLike
import com.typesafe.config.ConfigFactory
import io.github.alstanchev.pekko.persistence.inmemory.extension.{InMemoryJournalStorage, StorageExtensionProvider}
import org.apache.pekko.actor.Status
import org.apache.pekko.testkit.TestProbe

import scala.language.postfixOps

class BakerInquireSpec extends BakerPekkoRuntimeTestBase with BakerInquireSpecLike {

  override def actorSystemName = "BakerInquireSpec"

  val config = ConfigFactory.load()

  before {
    resetMocks()
    setupMockResponse()

    //clean the in-memory journal before each test
    val tp = TestProbe()
    tp.send(StorageExtensionProvider(defaultActorSystem).journalStorage(config), InMemoryJournalStorage.ClearJournal)
    tp.expectMsg(Status.Success(""))
  }
}