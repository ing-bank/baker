package com.ing.bakery.akka.persistence.cassandra

import java.net.InetSocketAddress
import java.util.UUID
import java.util.concurrent.atomic.AtomicBoolean

import akka.actor.ActorSystem
import akka.stream.alpakka.cassandra.{CqlSessionProvider, DefaultSessionProvider, DriverConfigLoaderFromConfig}
import com.codahale.metrics.jmx.JmxReporter
import com.datastax.oss.driver.api.core.CqlSession
import com.datastax.oss.driver.api.core.metadata.{Node, NodeStateListener}
import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters.toScala
import scala.concurrent.{ExecutionContext, Future}

case class Settings(
                     contactPoints: List[String],
                     port: Int,
                     username: String,
                     password: String,
                     profile: String,
                     localDatacenter: String,
                   )

object Settings {
  def apply(config: Config) =
    new Settings(
      contactPoints = config.getString("contact-points").split(",").map(_.trim).toList,
      port = config.getInt("port"),
      username = config.getString("username"),
      password = config.getString("password"),
      profile = config.getString("profile"),
      localDatacenter = config.getString("local-datacenter")
    )

}


class InstrumentedCassandraSessionProvider(system: ActorSystem,
                                           config: Config) extends DefaultSessionProvider(system, config) with LazyLogging {

  private val settings = Settings(
    system.classicSystem.settings.config.getConfig(config.getString("session-provider-config"))
  )

  private val jmxExporterInitialised = new AtomicBoolean(false)

  private val instanceId = UUID.randomUUID()

  override def connect()(implicit ec: ExecutionContext): Future[CqlSession] = {

    val nodeStateListener: NodeStateListener = new NodeStateListener {
      private def info(node: Node) = s"(host id: ${node.getHostId}, address ${node.getEndPoint.resolve()}, dc ${node.getDatacenter}, cassandra version ${node.getCassandraVersion})"

      override def onAdd(node: Node): Unit = logger.info(s"Node added ${info(node)}")

      override def onUp(node: Node): Unit = logger.info(s"Node up ${info(node)}")

      override def onDown(node: Node): Unit = logger.info(s"Node down ${info(node)}")

      override def onRemove(node: Node): Unit = logger.info(s"Node remove ${info(node)}")

      override def close(): Unit = logger.info(s"Listener closed")
    }

    def createConnection: Future[CqlSession] = {
      val driverConfig = CqlSessionProvider.driverConfig(system, config)
      val driverConfigLoader = DriverConfigLoaderFromConfig.fromConfig(driverConfig)
      logger.info("Creating new Cassandra connection")
      toScala(
        CqlSession.builder()
          .withConfigLoader(driverConfigLoader)
          .withAuthCredentials(settings.username, settings.password)
          .addContactPoints(settings.contactPoints.map(InetSocketAddress.createUnresolved(_, settings.port)).asJavaCollection)
          .withLocalDatacenter(settings.localDatacenter)
          .withClientId(instanceId)
          .withNodeStateListener(nodeStateListener)
          .buildAsync())

    }

    def instrumentConnection(connection: CqlSession): Future[Unit] = Future {
      jmxExporterInitialised.compareAndExchange(false, {
        lazy val maybeMetrics = connection.getMetrics

        if (maybeMetrics.isPresent) {
          val metrics = maybeMetrics.get()
          JmxReporter
            .forRegistry(metrics.getRegistry)
            .inDomain("com.datastax.oss.driver")
            .build
            .start()
          logger.info("Started JMX exporter")
        }
        true
      })
    }

    for {
      connection <- createConnection
      _ <- instrumentConnection(connection)
    } yield {
      connection
    }
  }
}
