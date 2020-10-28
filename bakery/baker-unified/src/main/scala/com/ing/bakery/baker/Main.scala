package com.ing.bakery.baker

import java.io.File
import java.net.InetSocketAddress
import java.util.concurrent.Executors

import akka.actor.ActorSystem
import akka.cluster.Cluster
import akka.stream.{ActorMaterializer, Materializer}
import cats.effect.{ExitCode, IO, IOApp, Resource}
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.runtime.akka.AkkaBakerConfig.KafkaEventSinkSettings
import com.ing.baker.runtime.akka.internal.{InteractionManager, InteractionManagerLocal}
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.bakery.interaction.BakeryHttp
import com.typesafe.config.ConfigFactory
import com.typesafe.scalalogging.LazyLogging
import javax.net.ssl.SSLContext
import kamon.Kamon
import net.ceedubs.ficus.Ficus._
import net.ceedubs.ficus.readers.ArbitraryTypeReader._
import org.http4s.client.blaze.BlazeClientBuilder
import org.springframework.context.annotation.AnnotationConfigApplicationContext
import skuber.api.client.KubernetesClient

import scala.concurrent.{ExecutionContext, Future}
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.runtime.scaladsl.InteractionInstance

import scala.collection.JavaConverters._

object Main extends IOApp with LazyLogging {

  override def run(args: List[String]): IO[ExitCode] = {
    Kamon.init()

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/bakery-application.conf")))

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
        logger.warn("No interactions configured, ")
      }
      (configurationClasses.asScala map { configurationClass =>
        val configClass = Class.forName(configurationClass)
        val ctx = new AnnotationConfigApplicationContext();
        ctx.register(configClass)
        ctx.refresh()
        val interactionsAsJavaMap: java.util.Map[String, Interaction] =
          ctx.getBeansOfType(classOf[com.ing.baker.recipe.javadsl.Interaction])
        val interactions = interactionsAsJavaMap.asScala.values.map(InteractionInstance.unsafeFrom).toList
        logger.info(s"$configurationClass: ${interactions.map(_.name).mkString(",")}")
        interactions
      } toList).flatten
    }

    val interactionManager = new InteractionManagerLocal(interactions)

    val mainResource: Resource[IO, Unit] =
      for {
        eventSink <- eventSinkResource
        baker = AkkaBaker
          .withConfig(AkkaBakerConfig(
            interactionManager = interactionManager,
            bakerActorProvider = AkkaBakerConfig.bakerProviderFrom(config),
            timeouts = AkkaBakerConfig.Timeouts.from(config),
            bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings.from(config),
          )(system))
        _ <- Resource.liftF(eventSink.attach(baker))
        _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(configPath, baker))
        _ <- Resource.liftF(IO.async[Unit] { callback =>
          Cluster(system).registerOnMemberUp {
            callback(Right(()))
          }
        })
        _ <- BakerService.resource(baker, hostname, apiUrlPrefix, interactionManager, loggingEnabled)
      } yield ()

    mainResource.use(_ => {
      logger.info("Baker initalisation complete, enabling the readiness")
      BakerReadinessCheck.enable()
      IO.never
    }
    ).as(ExitCode.Success)
  }
}
