package com.ing.baker.runtime.akka

import akka.actor.{ ActorSystem, Address, AddressFromURIString }
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl.{ CurrentEventsByPersistenceIdQuery, CurrentPersistenceIdsQuery, PersistenceIdsQuery }
import cats.data.NonEmptyList
import com.ing.baker.runtime.akka.AkkaBakerConfig.BakerPersistenceQuery
import com.ing.baker.runtime.akka.actor.serialization.Encryption
import com.ing.baker.runtime.akka.actor.{ BakerActorProvider, ClusterBakerActorProvider, LocalBakerActorProvider }
import com.ing.baker.runtime.akka.internal.InteractionManager
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._
import scala.concurrent.duration._

case class AkkaBakerConfig(
  defaultBakeTimeout: FiniteDuration,
  defaultProcessEventTimeout: FiniteDuration,
  defaultInquireTimeout: FiniteDuration,
  defaultShutdownTimeout: FiniteDuration,
  defaultAddRecipeTimeout: FiniteDuration,
  bakerActorProvider: BakerActorProvider,
  interactionManager: InteractionManager,
  readJournal: BakerPersistenceQuery
)(implicit val system: ActorSystem)

object AkkaBakerConfig {

  def localDefault(actorSystem: ActorSystem): AkkaBakerConfig =
    default(
      new LocalBakerActorProvider(
        retentionCheckInterval = 1.minute,
        ingredientsFilter = List.empty,
        actorIdleTimeout = Some(5.minutes),
        configuredEncryption = Encryption.NoEncryption
      ),
      actorSystem
    )

  def clusterDefault(seedNodes: NonEmptyList[Address], actorSystem: ActorSystem): AkkaBakerConfig =
    default(
      new ClusterBakerActorProvider(
        nrOfShards = 50,
        retentionCheckInterval = 1.minute,
        actorIdleTimeout = Some(5.minutes),
        ingredientsFilter = List.empty,
        journalInitializeTimeout = 30.seconds,
        seedNodes = ClusterBakerActorProvider.SeedNodesList(seedNodes),
        configuredEncryption = Encryption.NoEncryption
      ),
      actorSystem
    )

  def default(provider: BakerActorProvider, actorSystem: ActorSystem): AkkaBakerConfig = {
    AkkaBakerConfig(
      defaultBakeTimeout = 10.seconds,
      defaultProcessEventTimeout = 10.seconds,
      defaultInquireTimeout = 10.seconds,
      defaultShutdownTimeout = 30.seconds,
      defaultAddRecipeTimeout = 10.seconds,
      bakerActorProvider = provider,
      interactionManager = new InteractionManager(),
      readJournal = PersistenceQuery(actorSystem)
      .readJournalFor[BakerPersistenceQuery]("inmemory-read-journal")
    )(actorSystem)
  }

  def from(config: Config, actorSystem: ActorSystem): AkkaBakerConfig = {
    if (!config.getAs[Boolean]("baker.config-file-included").getOrElse(false))
      throw new IllegalStateException("You must 'include baker.conf' in your application.conf")
    AkkaBakerConfig(
      defaultBakeTimeout = config.as[FiniteDuration]("baker.bake-timeout"),
      defaultProcessEventTimeout = config.as[FiniteDuration]("baker.process-event-timeout"),
      defaultInquireTimeout = config.as[FiniteDuration]("baker.process-inquire-timeout"),
      defaultShutdownTimeout = config.as[FiniteDuration]("baker.shutdown-timeout"),
      defaultAddRecipeTimeout = config.as[FiniteDuration]("baker.add-recipe-timeout"),
      bakerActorProvider = {
        val encryption = {
          val encryptionEnabled = config.getAs[Boolean]("baker.encryption.enabled").getOrElse(false)
          if (encryptionEnabled) new Encryption.AESEncryption(config.as[String]("baker.encryption.secret"))
          else Encryption.NoEncryption
        }
        config.as[Option[String]]("baker.actor.provider") match {
          case None | Some("local") =>
            new LocalBakerActorProvider(
              retentionCheckInterval = config.as[FiniteDuration]("baker.actor.retention-check-interval"),
              ingredientsFilter = config.as[List[String]]("baker.filtered-ingredient-values"),
              actorIdleTimeout = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout"),
              encryption
            )
          case Some("cluster-sharded") =>
            new ClusterBakerActorProvider(
              nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards"),
              retentionCheckInterval = config.as[FiniteDuration]("baker.actor.retention-check-interval"),
              actorIdleTimeout = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout"),
              ingredientsFilter = config.as[List[String]]("baker.filtered-ingredient-values"),
              journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout"),
              seedNodes = {
                val seedList = config.as[Option[List[String]]]("baker.cluster.seed-nodes")
                if (seedList.isDefined)
                  ClusterBakerActorProvider.SeedNodesList(NonEmptyList.fromListUnsafe(seedList.get.map(AddressFromURIString.parse)))
                else
                  ClusterBakerActorProvider.ServiceDiscovery
              },
              configuredEncryption = encryption
            )
          case Some(other) => throw new IllegalArgumentException(s"Unsupported actor provider: $other")
        }
      },
      interactionManager = new InteractionManager,
      readJournal = PersistenceQuery(actorSystem)
        .readJournalFor[BakerPersistenceQuery](config.as[String]("baker.actor.read-journal-plugin"))
    )(actorSystem)
  }

  type BakerPersistenceQuery = CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery
}
