package com.ing.baker

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.TestRecipe._
import com.ing.baker.recipe.common.Recipe
import com.ing.baker.runtime.BakerRuntimeTestBase
import com.ing.baker.runtime.akka.PekkoBaker
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.core.util.CachingInteractionManager
import com.ing.baker.runtime.scaladsl.{Baker, InteractionInstance}
import com.typesafe.config.{Config, ConfigFactory}
import org.apache.pekko.actor.ActorSystem
import org.apache.pekko.testkit.TestKit

import java.util.UUID
import scala.concurrent.Future
import scala.concurrent.duration._
import scala.language.postfixOps

trait BakerPekkoRuntimeTestBase
  extends BakerRuntimeTestBase {

  protected def localLevelDBConfig(actorSystemName: String,
                                   journalInitializeTimeout: FiniteDuration = 10 seconds,
                                   journalPath: String = "target/journal",
                                   snapshotsPath: String = "target/snapshots"): Config =
    ConfigFactory.parseString(
      s"""
         |include "baker.conf"
         |
         |pekko {
         |
         |  actor {
         |    provider = "org.apache.pekko.actor.LocalActorRefProvider"
         |    allow-java-serialization = off
         |    serialize-messages = off
         |    serialize-creators = off
         |  }
         |
         |  persistence {
         |     journal.plugin = "pekko.persistence.journal.leveldb"
         |     journal.leveldb.dir = "$journalPath"
         |
         |     snapshot-store.plugin = "pekko.persistence.snapshot-store.local"
         |     snapshot-store.local.dir = "$snapshotsPath"
         |
         |     auto-start-snapshot-stores = [ "pekko.persistence.snapshot-store.local"]
         |     auto-start-journals = [ "pekko.persistence.journal.leveldb" ]
         |
         |     journal.leveldb.native = off
         |  }
         |
         |  loggers = ["org.apache.pekko.event.slf4j.Slf4jLogger"]
         |  loglevel = "DEBUG"
         |  logging-filter = "org.apache.pekko.event.slf4j.Slf4jLoggingFilter"
         |}
         |
         |baker {
         |  actor.provider = "local"
         |  actor.read-journal-plugin = "pekko.persistence.query.journal.leveldb"
         |  journal-initialize-timeout = $journalInitializeTimeout
         |
         |  recipe-manager-type = "actor"
         |}
         |
         |logging.root.level = DEBUG
    """.stripMargin)

  protected def clusterLevelDBConfig(actorSystemName: String,
                                     port: Int,
                                     journalInitializeTimeout: FiniteDuration = 10 seconds,
                                     journalPath: String = "target/journal",
                                     snapshotsPath: String = "target/snapshots"): Config =

    ConfigFactory.parseString(
      s"""
         |pekko {
         |
         |  actor.provider = "org.apache.pekko.cluster.ClusterActorRefProvider"
         |
         |  remote.artery {
         |    canonical.hostname = localhost
         |    canonical.port = $port
         |  }
         |}
         |
         |baker {
         |  actor.provider = "cluster-sharded"
         |  cluster.seed-nodes = ["pekko://$actorSystemName@localhost:$port"]
         |}
    """.stripMargin).withFallback(localLevelDBConfig(actorSystemName, journalInitializeTimeout, journalPath, snapshotsPath))

  implicit protected var defaultActorSystem: ActorSystem = ActorSystem(actorSystemName)

  override def afterAll(): Unit = {
    TestKit.shutdownActorSystem(defaultActorSystem)
  }

  /**
   * Returns a Baker instance that contains a simple recipe that can be used in tests
   * It als sets mocks that return happy flow responses for the interactions
   *
   * This recipe contains: See TestRecipe.png for a visualization
   *
   * @param recipeName A unique name that is needed for the recipe to insure that the tests do not interfere with each other
   * @return
   */
  protected def setupPekkoBakerWithRecipe(recipeName: String, appendUUIDToTheRecipeName: Boolean = true)
                                    (implicit actorSystem: ActorSystem): Future[(Baker, String)] = {
    val newRecipeName = if (appendUUIDToTheRecipeName) s"$recipeName-${UUID.randomUUID().toString}" else recipeName
    val recipe = getRecipe(newRecipeName)
    setupMockResponse()
    setupPekkoBakerWithRecipe(recipe, mockImplementations)(actorSystem)
  }

  protected def setupPekkoBakerWithRecipe(recipe: Recipe, implementations: List[InteractionInstance])
                                    (implicit actorSystem: ActorSystem): Future[(Baker, String)] = {
    val baker = PekkoBaker(ConfigFactory.load(), actorSystem, CachingInteractionManager(implementations))
    baker.addRecipe(RecipeRecord.of(RecipeCompiler.compileRecipe(recipe))).map(baker -> _)(actorSystem.dispatcher)
  }

  protected def setupPekkoBakerWithNoRecipe(implementations: List[InteractionInstance])(implicit actorSystem: ActorSystem): Future[Baker] = {
    setupMockResponse()
    Future.successful(PekkoBaker(ConfigFactory.load(), actorSystem, CachingInteractionManager(implementations)))
  }

  override protected def setupBakerWithRecipe(recipeName: String): Future[(Baker, String)] =
    setupPekkoBakerWithRecipe(recipeName)

  override protected def setupBakerWithRecipe(recipe: com.ing.baker.recipe.common.Recipe, implementations: List[InteractionInstance]): Future[(Baker, String)] =
    setupPekkoBakerWithRecipe(recipe, implementations)

  override protected def setupBakerWithoutRecipe(): Future[Baker] =
    setupPekkoBakerWithNoRecipe(mockImplementations)

  override protected def setupBakerWithoutRecipe(implementations: List[InteractionInstance]): Future[Baker] =
    setupPekkoBakerWithNoRecipe(implementations)
}