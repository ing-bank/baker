package com.ing.baker.runtime.akka.actor

import akka.Done
import akka.actor.ActorSystem
import akka.persistence.{SnapshotMetadata, cassandra}
import com.typesafe.scalalogging.LazyLogging

import scala.concurrent.{ExecutionContext, Future}

/**
  * The cleanup of Actor based data for Baker event store.
  * This abstraction iis build since for Cassandra we can use the Cassandra cleanup tool to cleanup the data in a optimized way.
  * For none Cassandra event stores we provide the ActorBasedBakerCleanup that uses the regular available cleanup for event stores.
  */
abstract class BakerCleanup {

  def supportsCleanupOfStoppedActors: Boolean

  def deleteAllEvents(persistenceId: String, neverUsePersistenceIdAgain: Boolean): Future[Done]

  def deleteEventsAndSnapshotBeforeSnapshot(persistenceId: String, maxSnapshotsToKeep: Int)(implicit ec: ExecutionContext): Future[Done]
}

class CassandraBakerCleanup(system: ActorSystem) extends BakerCleanup with LazyLogging {

  private val cleanup = new cassandra.cleanup.Cleanup(system)

  override def supportsCleanupOfStoppedActors = true

  override def deleteAllEvents(persistenceId: String, neverUsePersistenceIdAgain: Boolean): Future[Done] =
    cleanup.deleteAllEvents(persistenceId, neverUsePersistenceIdAgain)

  override def deleteEventsAndSnapshotBeforeSnapshot(persistenceId: String, maxSnapshotsToKeep: Int)(implicit ec: ExecutionContext): Future[Done] = {
    cleanup.deleteBeforeSnapshot(persistenceId, maxSnapshotsToKeep).flatMap {
      case Some(snapshotMetadata: SnapshotMetadata) =>
        //TODO Make this configurable instead of always deleting the message data
        logger.debug("SnapshotMetadata found, starting deleting messages")
        cleanup.deleteEventsTo(persistenceId, snapshotMetadata.sequenceNr)
      case None =>
        logger.debug("SnapshotMetadata not found")
        Future.successful(Done)
    }
  }
}

class ActorBasedBakerCleanup() extends BakerCleanup {

  override def supportsCleanupOfStoppedActors = false

  override def deleteAllEvents(persistenceId: String, neverUsePersistenceIdAgain: Boolean): Future[Done] = {
    Future.successful(Done)
  }

  override def deleteEventsAndSnapshotBeforeSnapshot(persistenceId: String, maxSnapshotsToKeep: Int)(implicit ec: ExecutionContext): Future[Done] = {
    //We did not remove old snapshots and messages before from actors so we do not do this without the CassandraCleanup tool
    Future.successful(Done)
  }
}
