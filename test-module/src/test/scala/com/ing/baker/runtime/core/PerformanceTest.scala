package com.ing.baker.runtime.core

import java.util.UUID
import java.util.concurrent.{Executors, TimeUnit}

import akka.actor.ActorSystem
import akka.persistence.cassandra.testkit.CassandraLauncher
import com.ing.baker.TestRecipeHelper
import com.typesafe.config.ConfigFactory

import scala.concurrent.{ExecutionContext, Future}
import scala.concurrent.duration.Duration

class PerformanceTest extends TestRecipeHelper {

  override def actorSystemName = "PerformanceTest"

  import com.codahale.metrics.MetricRegistry

  val metrics = new MetricRegistry

  import com.codahale.metrics.ConsoleReporter

  val reporter: ConsoleReporter = ConsoleReporter.forRegistry(metrics)
    .convertRatesTo(TimeUnit.SECONDS)
    .convertDurationsTo(TimeUnit.MILLISECONDS).build

  reporter.start(1, TimeUnit.SECONDS)

//  CassandraLauncher.start(
//    new java.io.File("target/cassandra"),
//    CassandraLauncher.DefaultTestConfigResource,
//    clean = true,
//    port = 9042,
//    CassandraLauncher.classpathForResources("logback-test.xml")
//  )

  Thread.sleep(10 * 1000)

  val cassandraConfig =
    s"""
       |
       |include "baker.conf"
       |
       |akka.persistence.journal.plugin = "cassandra-journal"
       |akka.persistence.snapshot-store.plugin = "cassandra-snapshot-store"
       |baker.actor.read-journal-plugin = "cassandra-query-journal"
       |
       |cassandra-journal.log-queries = off
       |cassandra-journal.keyspace-autocreate = off
       |cassandra-journal.tables-autocreate = off
       |
       |cassandra-snapshot-store.log-queries = off
       |cassandra-snapshot-store.keyspace-autocreate = off
       |cassandra-snapshot-store.tables-autocreate = off
       |
       |akka.loggers = ["akka.event.slf4j.Slf4jLogger"]
       |akka.loglevel = "DEBUG"
       |
       |
     """.stripMargin

  val akkaCassandraSystem = ActorSystem("A", ConfigFactory.parseString(cassandraConfig))

  "Baker" should {

    "should bake really fast" in {

      val (baker, recipeId) = setupBakerWithRecipe("R")(akkaCassandraSystem)

      val nrOfBakes = 5 * 1000
      val nrOfThreads = 8

      val executionContext = ExecutionContext.fromExecutor(Executors.newFixedThreadPool(nrOfThreads))

      // warmup

      println("Warming up baker with 10 bakes")
      (1 to 10).foreach { _ =>
        baker.bake(recipeId, UUID.randomUUID().toString)
      }

      val bakeTimer = metrics.timer(MetricRegistry.name("PerformanceTest", "bake"))

      println("Starting stress testing")



      // stress testing
      (1 to nrOfBakes).foreach { _ =>

        executionContext.execute { () =>

          val time = bakeTimer.time()

          try {
            baker.bake(recipeId, UUID.randomUUID().toString)
          } finally {
            time.stop()
          }
        }

      }

      Thread.sleep(1000 * 60)
    }
  }
}
