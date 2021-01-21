package com.ing.bakery.baker

import java.net.InetSocketAddress
import akka.actor.{Actor, ActorLogging, ActorSystem, Props}
import akka.cluster.Cluster
import akka.cluster.ClusterEvent._
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.bakery.metrics.MetricService
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import org.cassandraunit.utils.EmbeddedCassandraServerHelper.startEmbeddedCassandra
import org.http4s.server.Server
import org.springframework.context.annotation.AnnotationConfigApplicationContext

import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext

object MainMetrics extends IOApp with LazyLogging {
  val cassandra = startEmbeddedCassandra("cassandra-server.yaml")

  override def run(args: List[String]): IO[ExitCode] = {
    val config = ConfigFactory.load()
    val bakery = config.getConfig("baker")

    implicit val system: ActorSystem = ActorSystem("test", config)
    implicit val executionContext: ExecutionContext = system.dispatcher
    system.actorOf(Props[ClusterEventWatch], name = "ClusterListener")

    val metricsPort = bakery.getInt("metrics-port")
    val loggingEnabled = bakery.getBoolean("api-logging-enabled")
    logger.info(s"Logging of API: $loggingEnabled  - MUST NEVER BE SET TO 'true' IN PRODUCTION")

    val configurationClasses = bakery.getStringList("interaction-configuration-classes")

    val interactions = {
      (configurationClasses.asScala map { configurationClass =>
        val configClass = Class.forName(configurationClass)
        val ctx = new AnnotationConfigApplicationContext()
        ctx.register(configClass)
        ctx.refresh()
        val interactionsAsJavaMap: java.util.Map[String, Interaction] =
          ctx.getBeansOfType(classOf[com.ing.baker.recipe.javadsl.Interaction])
        val interactions = interactionsAsJavaMap.asScala.values.map(InteractionInstance.unsafeFrom).toList
        logger.info(s"Loaded ${interactions.size} interactions from $configurationClass: ${interactions.sortBy(_.name).map(_.name).mkString(",")}")
        interactions
      } toList).flatten
    }

    val interactionManager = LocalInteractions(interactions)

    val bakerConfig = AkkaBakerConfig(
      interactions = interactionManager,
      bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
      timeouts = AkkaBakerConfig.Timeouts.apply(config),
      bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config)
    )(system)

    logger.info("Starting Akka Baker...")
    val baker = AkkaBaker.withConfig(bakerConfig)

    val mainResource: Resource[IO, Server[IO]] =
      for {
        _ <- Resource.liftF(IO.async[Unit] { callback =>
          Cluster(system).registerOnMemberUp {
            logger.info("Akka cluster is now up")
            callback(Right(()))
          }
        })
        metricsService <- MetricService.resource(
          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
        )
      } yield metricsService

    mainResource.use(metricService => {
      logger.info(s"Bakery started at ${metricService.address}/${metricService.baseUri}, enabling the readiness in Akka management")
      BakerReadinessCheck.enable()
      IO.never
    }
    ).as(ExitCode.Success)
  }
}
