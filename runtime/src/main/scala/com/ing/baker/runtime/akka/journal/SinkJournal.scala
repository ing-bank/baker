package com.ing.baker.runtime.akka.journal

import akka.persistence.{AtomicWrite, PersistentRepr, SelectedSnapshot, SnapshotMetadata, SnapshotSelectionCriteria}
import akka.persistence.journal.AsyncWriteJournal
import akka.persistence.snapshot.SnapshotStore


import scala.collection.immutable
import scala.concurrent.Future
import scala.util.Try

class SinkJournalWriter extends AsyncWriteJournal {

  override def asyncWriteMessages(messages: immutable.Seq[AtomicWrite]): Future[immutable.Seq[Try[Unit]]] =
    Future.successful(immutable.Seq.empty[Try[Unit]])

  override def asyncDeleteMessagesTo(persistenceId: String, toSequenceNr: Long): Future[Unit] =
    Future.unit

  override def asyncReplayMessages(persistenceId: String, fromSequenceNr: Long, toSequenceNr: Long, max: Long)(recoveryCallback: PersistentRepr => Unit): Future[Unit] =
    Future.unit

  override def asyncReadHighestSequenceNr(persistenceId: String, fromSequenceNr: Long): Future[Long] =
    Future.successful(0)
}

class SinkSnapshotStore extends SnapshotStore {

  override def loadAsync(persistenceId: String, criteria: SnapshotSelectionCriteria): Future[Option[SelectedSnapshot]] =
    Future.successful(None)

  override def saveAsync(metadata: SnapshotMetadata, snapshot: Any): Future[Unit] =
    Future.unit

  override def deleteAsync(metadata: SnapshotMetadata): Future[Unit] =
    Future.unit

  override def deleteAsync(persistenceId: String, criteria: SnapshotSelectionCriteria): Future[Unit] =
    Future.unit
}


