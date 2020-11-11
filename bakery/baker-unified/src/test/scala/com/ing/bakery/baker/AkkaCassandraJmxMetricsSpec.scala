package com.ing.bakery.baker


import java.io.CharArrayWriter
import java.net.InetSocketAddress
import java.util.UUID

import akka.actor.{ActorLogging, ActorSystem, NoSerializationVerificationNeeded, Props}
import akka.pattern.ask
import akka.persistence.PersistentActor
import akka.util.Timeout
import com.datastax.oss.driver.api.core.CqlSession
import com.datastax.oss.driver.api.querybuilder.QueryBuilder._
import com.datastax.oss.driver.api.querybuilder.term.Term
import com.typesafe.scalalogging.LazyLogging
import io.prometheus.client.exporter.common.TextFormat
import org.cassandraunit.utils.EmbeddedCassandraServerHelper._
import org.scalatest.concurrent.Eventually
import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.time.{Millis, Seconds, Span}

import scala.Console.println
import scala.collection.JavaConverters._
import scala.collection.convert.ImplicitConversions._
import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext}

class AkkaCassandraJmxMetricsSpec extends AnyFreeSpec with LazyLogging with Eventually {

  import TestActors._
  implicit override val patienceConfig: PatienceConfig =
    PatienceConfig(timeout = scaled(Span(2, Seconds)), interval = scaled(Span(5, Millis)))

  val cassandra = {
    try {
      startEmbeddedCassandra("cassandra-server.yaml")
    } catch {
      case e: Exception =>
    }
  }
  implicit val ec: ExecutionContext = ExecutionContext.global
  private val system: ActorSystem = ActorSystem("test")
  private val persistenceInitActor = system.actorOf(Props(classOf[AwaitPersistenceInit]), s"persistenceInit-${UUID.randomUUID().toString}")

  def createSession = {
    CqlSession.builder()
      .withLocalDatacenter("datacenter1")
      .addContactPoints(List(InetSocketAddress.createUnresolved(getHost, getNativeTransportPort)).asJavaCollection)
      .build()
  }

  "Launch cassandra and akka app, and ensure it works" - {

    "starts actor system and pings the bootstrap actor" in {
      pingActor
    }

    "after some activity exports some jmx metrics" in {
      val session = createSession
      session.execute("create table akka.test (id int, a text, b text, primary key(id))")
      for (i <- 1 to 100) {
        session
          .execute(
            insertInto("akka", "test")
              .values(Map[String, Term](
                "id" -> literal(i),
                "a" -> literal(s"A${i}"),
                "b" -> literal(s"B$i")).asJava).build()
          )
      }

      import java.lang.management.ManagementFactory
      val mbs = ManagementFactory.getPlatformMBeanServer
      mbs.queryMBeans(null, null).map(_.getObjectName).filter(_.toString.startsWith("akka")).foreach(println)
      val datastaxMbeans = mbs.queryMBeans(null, null).filter(_.getObjectName.getDomain == "com.datastax.oss.driver")
//      datastaxMbeans.foreach(println)
      assert(datastaxMbeans.nonEmpty)
    }

    "ensure prometheus JMX scraping is working" in {

      for (i <- 1 to 100000) {
        pingActor
      }
      val prometheusRegistry = MetricService.registry

      val writer = new CharArrayWriter(16 * 1024)
      TextFormat.write004(writer, prometheusRegistry.metricFamilySamples)
      val content = writer.toString
      println(content)
      assert(content.split("\n").exists(_.startsWith("cassandra_cql")))
    }

  }


  private def pingActor = {
    val r = Await.result(persistenceInitActor.ask(Ping)(Timeout.durationToTimeout(30 seconds)), 40 seconds)
    assert(r.toString == "Pong")
  }
}

object TestActors {

  case object Ping extends NoSerializationVerificationNeeded

  case object Pong extends NoSerializationVerificationNeeded

  class AwaitPersistenceInit extends PersistentActor with ActorLogging {

    override val persistenceId: String = s"persistenceInit-${UUID.randomUUID()}"

    log.info("Starting PersistenceInit actor with id: {}", persistenceId)

    // intentionally left empty
    def receiveRecover: Receive = Map.empty

    // intentionally left empty
    def receiveCommand: Receive = {
      case Ping =>
        sender() ! Pong
    }
  }


}