package com.ing.baker.runtime.core

import java.util.UUID
import java.util.concurrent.{Executors, TimeUnit}

import akka.actor.ActorSystem
import akka.persistence.cassandra.testkit.CassandraLauncher
import com.ing.baker.TestRecipeHelper
import com.typesafe.config.ConfigFactory

import scala.concurrent.ExecutionContext

class PerformanceTest extends TestRecipeHelper {

  override def actorSystemName = "PerformanceTest"

  import com.codahale.metrics.MetricRegistry

  val metrics = new MetricRegistry

  import com.codahale.metrics.ConsoleReporter

  val reporter: ConsoleReporter = ConsoleReporter.forRegistry(metrics)
    .convertRatesTo(TimeUnit.SECONDS)
    .convertDurationsTo(TimeUnit.MILLISECONDS).build

  reporter.start(1, TimeUnit.SECONDS)

  CassandraLauncher.start(
    new java.io.File("target/cassandra"),
    CassandraLauncher.DefaultTestConfigResource,
    clean = true,
    port = 9042,
    CassandraLauncher.classpathForResources("logback.xml")
  )

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
     """.stripMargin

  val akkaCassandraSystem = ActorSystem("PerformanceTestActorSystem", ConfigFactory.parseString(cassandraConfig))

  "Baker" should {

    "should bake really fast" in {

      val (baker, recipeId) = setupBakerWithRecipe("BakePerformanceTestRecipe")(akkaCassandraSystem)

      val nrOfBakes = 1000 //* 1000
      val nrOfThreads = 8

      val executionContext = ExecutionContext.fromExecutor(Executors.newFixedThreadPool(nrOfThreads))

      val bakeTimer = metrics.timer(MetricRegistry.name(classOf[PerformanceTest], "bake"))

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
