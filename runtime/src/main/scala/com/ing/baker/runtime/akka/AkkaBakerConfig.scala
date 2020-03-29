package com.ing.baker.runtime.akka

import akka.actor.{ActorSystem, Address, AddressFromURIString}
import akka.persistence.query.PersistenceQuery
import akka.persistence.query.scaladsl.{CurrentEventsByPersistenceIdQuery, CurrentPersistenceIdsQuery, PersistenceIdsQuery}
import cats.data.NonEmptyList
import com.ing.baker.runtime.akka.AkkaBakerConfig.{BakerPersistenceQuery, BakerValidationSettings, EventSinkSettings}
import com.ing.baker.runtime.akka.actor.{BakerActorProvider, ClusterBakerActorProvider, LocalBakerActorProvider}
import com.ing.baker.runtime.akka.internal.{InteractionManager, InteractionManagerLocal}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import net.ceedubs.ficus.Ficus._

import scala.concurrent.duration._

case class AkkaBakerConfig(
                            bakerActorProvider: BakerActorProvider,
                            interactionManager: InteractionManager,
                            readJournal: BakerPersistenceQuery,
                            timeouts: AkkaBakerConfig.Timeouts,
                            bakerValidationSettings: BakerValidationSettings
                          )(implicit val system: ActorSystem)

object AkkaBakerConfig extends LazyLogging {

  case class KafkaEventSinkSettings(`bootstrap-servers`: String, `bakery-events-topic`: String, `recipe-events-topic`: String)
  case class InternalEventSinkSettings(`last-events-to-keep`: Int)
  case class EventSinkSettings(internal: InternalEventSinkSettings, kafka: Option[KafkaEventSinkSettings])

  case class BakerValidationSettings(allowAddingRecipeWithoutRequiringInstances: Boolean)

  object BakerValidationSettings {
    def default: BakerValidationSettings = BakerValidationSettings(false)

    def from(config: Config): BakerValidationSettings =
      BakerValidationSettings(config.getOrElse[Boolean]("baker.allow-adding-recipe-without-requiring-instances", false))
  }

  case class Timeouts(
                       defaultBakeTimeout: FiniteDuration,
                       defaultProcessEventTimeout: FiniteDuration,
                       defaultInquireTimeout: FiniteDuration,
                       defaultShutdownTimeout: FiniteDuration,
                       defaultAddRecipeTimeout: FiniteDuration
                     )

  object Timeouts {

    def default: Timeouts =
      Timeouts(
        defaultBakeTimeout = 10.seconds,
        defaultProcessEventTimeout = 10.seconds,
        defaultInquireTimeout = 10.seconds,
        defaultShutdownTimeout = 30.seconds,
        defaultAddRecipeTimeout = 10.seconds,
      )

    def from(config: Config) =
      Timeouts(
        defaultBakeTimeout = config.as[FiniteDuration]("baker.bake-timeout"),
        defaultProcessEventTimeout = config.as[FiniteDuration]("baker.process-event-timeout"),
        defaultInquireTimeout = config.as[FiniteDuration]("baker.process-inquire-timeout"),
        defaultShutdownTimeout = config.as[FiniteDuration]("baker.shutdown-timeout"),
        defaultAddRecipeTimeout = config.as[FiniteDuration]("baker.add-recipe-timeout")
      )
  }

  def localDefault(actorSystem: ActorSystem): AkkaBakerConfig = {
    val localProvider =
      new LocalBakerActorProvider(
        retentionCheckInterval = 1.minute,
        ingredientsFilter = List.empty,
        actorIdleTimeout = Some(5.minutes),
        configuredEncryption = Encryption.NoEncryption
      )
    AkkaBakerConfig(
      timeouts = Timeouts.default,
      bakerValidationSettings = BakerValidationSettings.default,
      bakerActorProvider = localProvider,
      interactionManager = new InteractionManagerLocal(),
      readJournal = PersistenceQuery(actorSystem)
        .readJournalFor[BakerPersistenceQuery]("inmemory-read-journal")
    )(actorSystem)
  }

  def clusterDefault(seedNodes: NonEmptyList[Address], actorSystem: ActorSystem): AkkaBakerConfig = {
    val clusterProvider =
      new ClusterBakerActorProvider(
        nrOfShards = 50,
        retentionCheckInterval = 1.minute,
        actorIdleTimeout = Some(5.minutes),
        ingredientsFilter = List.empty,
        journalInitializeTimeout = 30.seconds,
        seedNodes = ClusterBakerActorProvider.SeedNodesList(seedNodes),
        configuredEncryption = Encryption.NoEncryption
      )
    AkkaBakerConfig(
      timeouts = Timeouts.default,
      bakerValidationSettings = BakerValidationSettings.default,
      bakerActorProvider = clusterProvider,
      interactionManager = new InteractionManagerLocal(),
      readJournal = PersistenceQuery(actorSystem)
        .readJournalFor[BakerPersistenceQuery]("inmemory-read-journal")
    )(actorSystem)
  }

  def from(config: Config, actorSystem: ActorSystem): AkkaBakerConfig = {
    if (!config.getAs[Boolean]("baker.config-file-included").getOrElse(false))
      throw new IllegalStateException("You must 'include baker.conf' in your application.conf")
    AkkaBakerConfig(
      timeouts = Timeouts.from(config),
      bakerValidationSettings = BakerValidationSettings.from(config),
      bakerActorProvider = bakerProviderFrom(config),
      interactionManager = interactionManagerFrom(config),
      readJournal = persistenceQueryFrom(config, actorSystem)
    )(actorSystem)
  }

  def bakerProviderFrom(config: Config): BakerActorProvider = {
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
  }

  def interactionManagerFrom(config: Config): InteractionManager = {
    new InteractionManagerLocal()
  }

  def persistenceQueryFrom(config: Config, system: ActorSystem): BakerPersistenceQuery = {
    PersistenceQuery(system)
      .readJournalFor[BakerPersistenceQuery](config.as[String]("baker.actor.read-journal-plugin"))
  }

  type BakerPersistenceQuery = CurrentEventsByPersistenceIdQuery with PersistenceIdsQuery with CurrentPersistenceIdsQuery
}
