package com.ing.baker.runtime.akka.journal

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should

import scala.collection.immutable.Seq

class SinkJournalAndSnapshotSpec extends AnyFlatSpec with should.Matchers {

  "SinkJournalWriter" should "not crash" in {
    val sjw = new Object with SinkJournalWriterImpl
    sjw.asyncWriteMessages(Seq.empty)
    sjw.asyncDeleteMessagesTo("", 0L)
    sjw.asyncReplayMessages("", 0L, 0L, 0L)(_ => ())
    sjw.asyncReadHighestSequenceNr("", 0L)
  }

  "SinkSnapshotStore" should "not crash" in {
    val sss = new Object with SinkSnapshotStoreImpl
    sss.loadAsync("", null)
    sss.saveAsync(null, null)
    sss.deleteAsync(null)
    sss.deleteAsync(null, null)
  }
}
