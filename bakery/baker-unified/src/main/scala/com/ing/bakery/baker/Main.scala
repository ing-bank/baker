package com.ing.bakery.baker

import java.io.File
import java.net.InetSocketAddress

import akka.actor.ActorSystem
import akka.cluster.Cluster
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.internal.InteractionManagerLocal
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import kamon.Kamon
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.server.Server
import org.springframework.context.annotation.AnnotationConfigApplicationContext

import scala.collection.JavaConverters._
import scala.concurrent.ExecutionContext

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))

    val eventSinkSettings = config.getConfig("baker.kafka-event-sink").as[KafkaEventSinkSettings]
    val eventSinkResource = KafkaEventSink.resource(eventSinkSettings)
    val bakery = config.getConfig("bakery")

    val httpServerPort = bakery.getInt("http-api-port")
    val apiUrlPrefix = bakery.getString("api-url-prefix")
    val configurationClasses = bakery.getStringList("interaction-configuration-classes")

    implicit val system: ActorSystem = ActorSystem("baker", config)
    implicit val executionContext: ExecutionContext = system.dispatcher

    val hostname: InetSocketAddress = InetSocketAddress.createUnresolved("0.0.0.0", httpServerPort)

    val loggingEnabled = bakery.getBoolean("api-logging-enabled")
    logger.info(s"Logging of API: ${loggingEnabled}  - MUST NEVER BE SET TO 'true' IN PRODUCTION")

    val interactions = {
      if (configurationClasses.size() == 0) {
        logger.warn("No interactions configured, probably interaction-configuration-classes config parameter is empty")
      }
      (configurationClasses.asScala map { configurationClass =>
        val configClass = Class.forName(configurationClass)
        val ctx = new AnnotationConfigApplicationContext();
        ctx.register(configClass)
        ctx.refresh()
        val interactionsAsJavaMap: java.util.Map[String, Interaction] =
          ctx.getBeansOfType(classOf[com.ing.baker.recipe.javadsl.Interaction])
        val interactions = interactionsAsJavaMap.asScala.values.map(InteractionInstance.unsafeFrom).toList
        logger.info(s"Loaded ${interactions.size} interactions from $configurationClass: ${interactions.sortBy(_.name).map(_.name).mkString(",")}")
        interactions
      } toList).flatten
    }

    val interactionManager = new InteractionManagerLocal(interactions)

    val bakerConfig = AkkaBakerConfig(
      interactionManager = interactionManager,
      bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
      timeouts = AkkaBakerConfig.Timeouts.from(config),
      bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config)
    )(system)

    logger.info("Starting Akka Baker...")
    val baker = AkkaBaker.withConfig(bakerConfig)
    logger.info("Starting recipe loader...")
    RecipeLoader.loadRecipesIntoBaker(configPath, baker)

    logger.info("Initialising Bakery...")
    val mainResource: Resource[IO, Server[IO]] =
      for {
        eventSink <- eventSinkResource
        _ <- Resource.liftF(eventSink.attach(baker))
        _ <- Resource.liftF(IO.async[Unit] { callback =>
          logger.info("Registering cluster-up callback")
          Cluster(system).registerOnMemberUp {
            logger.info("Akka cluster is up")
            callback(Right(()))
          }
        })
        bakerService <- BakerService.resource(baker, hostname, apiUrlPrefix, interactionManager, loggingEnabled)
      } yield bakerService

    logger.info("Starting Bakery...")
    mainResource.use(bakery => {
      logger.info(s"Bakery started at ${bakery.address}/${bakery.baseUri}, enabling the readiness in Akka management")
      BakerReadinessCheck.enable()
      IO.never
    }
    ).as(ExitCode.Success)
  }
}
