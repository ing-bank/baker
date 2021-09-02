package com.ing.baker.runtime.akka

import akka.actor.{ActorSystem, Address, AddressFromURIString}
import cats.data.NonEmptyList
import cats.effect.IO
import com.ing.baker.runtime.akka.AkkaBakerConfig.BakerValidationSettings
import com.ing.baker.runtime.akka.actor.{BakerActorProvider, ClusterBakerActorProvider, LocalBakerActorProvider}
import com.ing.baker.runtime.akka.internal.CachedInteractionManager
import com.ing.baker.runtime.model.InteractionManager
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ValueReader

import scala.concurrent.duration._

case class AkkaBakerConfig(
                            bakerActorProvider: BakerActorProvider,
                            interactions: InteractionManager[IO],
                            timeouts: AkkaBakerConfig.Timeouts,
                            bakerValidationSettings: BakerValidationSettings
                          )(implicit val system: ActorSystem)

object AkkaBakerConfig extends LazyLogging {

  case class KafkaEventSinkSettings(enabled: Boolean, `bootstrap-servers`: String, `baker-events-topic`: String, `recipe-events-topic`: String)

  case class BakerValidationSettings(allowAddingRecipeWithoutRequiringInstances: Boolean)

  case object ActorRecipeManagerType extends RecipeManagerType

  case object InMemoryRecipeManagerType extends RecipeManagerType

  sealed trait RecipeManagerType

  implicit val recipeManagerTypeReader: ValueReader[RecipeManagerType] = (config: Config, path: String) => {
    if (config.hasPath(path) && config.getString(path) == "inmemory") InMemoryRecipeManagerType
    else ActorRecipeManagerType
  }

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

    def apply(config: Config): Timeouts =
      Timeouts(
        defaultBakeTimeout = config.as[FiniteDuration]("baker.bake-timeout"),
        defaultProcessEventTimeout = config.as[FiniteDuration]("baker.process-event-timeout"),
        defaultInquireTimeout = config.as[FiniteDuration]("baker.process-inquire-timeout"),
        defaultShutdownTimeout = config.as[FiniteDuration]("baker.shutdown-timeout"),
        defaultAddRecipeTimeout = config.as[FiniteDuration]("baker.add-recipe-timeout")
      )
  }

  def localDefault(actorSystem: ActorSystem): AkkaBakerConfig = {
    localDefault(actorSystem, CachedInteractionManager())
  }

  def localDefault(actorSystem: ActorSystem, interactions: CachedInteractionManager): AkkaBakerConfig = {
    val defaultTimeouts = Timeouts.default

    val localProvider =
      new LocalBakerActorProvider(
        retentionCheckInterval = 1.minute,
        ingredientsFilter = List.empty,
        actorIdleTimeout = Some(5.minutes),
        configuredEncryption = Encryption.NoEncryption,
        timeouts = defaultTimeouts,
        recipeManagerType = InMemoryRecipeManagerType
      )

    AkkaBakerConfig(
      timeouts = defaultTimeouts,
      bakerValidationSettings = BakerValidationSettings.default,
      bakerActorProvider = localProvider,
      interactions = interactions
    )(actorSystem)
  }

  def clusterDefault(seedNodes: NonEmptyList[Address],
                     actorSystem: ActorSystem,
                     interactions: CachedInteractionManager): AkkaBakerConfig = {
    val defaultTimeouts = Timeouts.default

    val clusterProvider =
      new ClusterBakerActorProvider(
        nrOfShards = 50,
        retentionCheckInterval = 1.minute,
        actorIdleTimeout = Some(5.minutes),
        ingredientsFilter = List.empty,
        journalInitializeTimeout = 30.seconds,
        seedNodes = ClusterBakerActorProvider.SeedNodesList(seedNodes),
        configuredEncryption = Encryption.NoEncryption,
        timeouts = defaultTimeouts,
        recipeManagerType = ActorRecipeManagerType
      )

    AkkaBakerConfig(
      timeouts = defaultTimeouts,
      bakerValidationSettings = BakerValidationSettings.default,
      bakerActorProvider = clusterProvider,
      interactions = interactions
    )(actorSystem)
  }

  def from(config: Config, actorSystem: ActorSystem, interactions: CachedInteractionManager): AkkaBakerConfig = {
    if (!config.getAs[Boolean]("baker.config-file-included").getOrElse(false))
      throw new IllegalStateException("You must 'include baker.conf' in your application.conf")

    AkkaBakerConfig(
      timeouts = Timeouts.apply(config),
      bakerValidationSettings = BakerValidationSettings.from(config),
      bakerActorProvider = bakerProviderFrom(config),
      interactions = interactions
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
          configuredEncryption = encryption,
          timeouts = Timeouts.default,
          recipeManagerType = config.as[RecipeManagerType]("baker.recipe-manager-type")
        )
      case Some("cluster-sharded") =>
        new ClusterBakerActorProvider(
          nrOfShards = config.as[Int]("baker.actor.cluster.nr-of-shards"),
          retentionCheckInterval = config.as[FiniteDuration]("baker.actor.retention-check-interval"),
          actorIdleTimeout = config.as[Option[FiniteDuration]]("baker.actor.idle-timeout"),
          journalInitializeTimeout = config.as[FiniteDuration]("baker.journal-initialize-timeout"),
          seedNodes = {
            val seedList = config.as[Option[List[String]]]("baker.cluster.seed-nodes")
            if (seedList.isDefined)
              ClusterBakerActorProvider.SeedNodesList(NonEmptyList.fromListUnsafe(seedList.get.map(AddressFromURIString.parse)))
            else
              ClusterBakerActorProvider.ServiceDiscovery
          },
          ingredientsFilter = config.as[List[String]]("baker.filtered-ingredient-values"),
          configuredEncryption = encryption,
          Timeouts.default,
          recipeManagerType = config.as[RecipeManagerType]("baker.recipe-manager-type")
        )
      case Some(other) => throw new IllegalArgumentException(s"Unsupported actor provider: $other")
    }
  }
}
