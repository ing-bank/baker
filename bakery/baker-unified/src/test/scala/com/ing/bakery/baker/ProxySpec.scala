package com.ing.bakery.baker

import akka.actor.ActorSystem
import cats.effect.{ContextShift, IO, Resource, Timer}
import com.ing.baker.runtime.akka.internal.LocalInteractions
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.bakery.mocks.EventListener
import com.ing.bakery.testing.BakeryFunSpec
import com.typesafe.config.ConfigFactory
import org.http4s.Status.Ok
import org.http4s.client.blaze.BlazeClientBuilder

import java.io.File
import java.net.InetSocketAddress
import java.util.UUID
import scala.concurrent.ExecutionContext

class ProxySpec extends BakeryFunSpec {
  test("Proxy service available") { client =>

        client.get(s"http://localhost:$metricsPort") {
          case Ok(_) => IO.unit
          case _ =>  IO.raiseError(new IllegalStateException("Not started"))
        }

  }
  def contextBuilder(testArguments: TestArguments): Resource[IO, TestContext] = {

    val configPath = sys.env.getOrElse("CONFIG_DIRECTORY", "/opt/docker/conf")
    val config = ConfigFactory.load(ConfigFactory.parseFile(new File(s"$configPath/application.conf")))
    val bakery = config.getConfig("baker")
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    implicit val cs: ContextShift[IO] = IO.contextShift(executionContext)
    implicit val timer: Timer[IO] = IO.timer(executionContext)
    val metricsPort = bakery.getInt("metrics-port")
    val mainResource  =
      for {
        httpClient <- BlazeClientBuilder[IO](executionContext).resource
        proxyService <- ApiProxy.resource(
          InetSocketAddress.createUnresolved("0.0.0.0", metricsPort)
        )
        makeActorSystem = IO {
          ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
            """
              |akka {
              |  stdout-loglevel = "OFF"
              |  loglevel = "OFF"
              |}
              |""".stripMargin)) }
        stopActorSystem = (system: ActorSystem) => IO.fromFuture(IO {
          system.terminate().flatMap(_ => system.whenTerminated) }).void
        system <- Resource.make(makeActorSystem)(stopActorSystem)
        baker = AkkaBaker
          .withConfig(AkkaBakerConfig.localDefault(system).copy(
            interactions = LocalInteractions(),
            bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings(
              allowAddingRecipeWithoutRequiringInstances = true))(system)
          )

        server <- BakerService.resource(baker, InetSocketAddress.createUnresolved("127.0.0.1", 0), "/api/bakery",
          LocalInteractions(), loggingEnabled = true)

      } yield httpClient

    def getResourceDirectoryPathSafe: String = {
      val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
      val safePath = getClass.getResource("/recipes").getPath
      if (isWindows) safePath.tail
      else safePath
    }

    for {
      // Mock server
      mockServer <- Resource.make(IO(ClientAndServer.startClientAndServer(0)))(s => IO(s.stop()))
      remoteInteraction = new RemoteInteraction(mockServer)
      kubeApiServer = new KubeApiServer(mockServer)
      _ <- Resource.liftF(kubeApiServer.noNewInteractions()) // Initial setup so that the service discovery component has something to query to immediately

      makeActorSystem = IO {
        ActorSystem(UUID.randomUUID().toString, ConfigFactory.parseString(
          """
            |akka {
            |  stdout-loglevel = "OFF"
            |  loglevel = "OFF"
            |}
            |""".stripMargin)) }
      stopActorSystem = (system: ActorSystem) => IO.fromFuture(IO {
        system.terminate().flatMap(_ => system.whenTerminated) }).void
      system <- Resource.make(makeActorSystem)(stopActorSystem)

      k8s: KubernetesClient = skuber.k8sInit(skuber.api.Configuration.useLocalProxyOnPort(mockServer.getLocalPort))(system)
      httpClient <- BlazeClientBuilder[IO](executionContext).resource
      interactionDiscovery <-
        InteractionDiscovery.resource(httpClient, k8s, LocalInteractions(),
          List.empty, Some( LabelSelector(LabelSelector.IsEqualRequirement("scope","webshop"))))(contextShift, timer, system)

      eventListener = new EventListener()
      baker = AkkaBaker
        .withConfig(AkkaBakerConfig.localDefault(system).copy(
          interactions = interactionDiscovery,
          bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings(
            allowAddingRecipeWithoutRequiringInstances = true))(system)
        )

      _ <- Resource.liftF(eventListener.eventSink.attach(baker))
      _ <- Resource.liftF(RecipeLoader.loadRecipesIntoBaker(getResourceDirectoryPathSafe, baker))

      server <- BakerService.resource(baker, InetSocketAddress.createUnresolved("127.0.0.1", 0), "/api/bakery", interactionDiscovery, loggingEnabled = true)
      client <- BakerClient.resource(server.baseUri, "/api/bakery", executionContext)

    } yield Context(
      client,
      remoteInteraction,
      interactionDiscovery,
      eventListener,
      kubeApiServer
    )
  }

}

