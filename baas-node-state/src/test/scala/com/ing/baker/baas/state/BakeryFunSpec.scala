package com.ing.baker.baas.state

import java.util.UUID

import akka.actor.ActorSystem
import akka.http.scaladsl.Http.ServerBinding
import akka.http.scaladsl.model.Uri
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.baas.mocks.{KubeApiServer, RemoteComponents, RemoteEventListener, RemoteInteraction}
import com.ing.baker.baas.recipe.Interactions
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory
import io.kubernetes.client.openapi.ApiClient
import org.jboss.netty.channel.ChannelException
import org.mockserver.integration.ClientAndServer.startClientAndServer
import org.scalactic.source
import org.scalatest.compatible.Assertion
import org.scalatest.{AsyncFunSpecLike, Tag}

import scala.concurrent.duration.{FiniteDuration, _}
import scala.concurrent.{Future, Promise}
import scala.util.Success

abstract class BakeryFunSpec extends AsyncFunSpecLike {

  implicit val contextShift: ContextShift[IO] =
    IO.contextShift(executionContext)

  implicit val timer: Timer[IO] =
    IO.timer(executionContext)

  def eventually[A](f: => Future[A]): Future[A] =
    within(5.seconds)(f)

  def within[A](time: FiniteDuration)(f: => Future[A]): Future[A] = {
    def inner(count: Int, times: FiniteDuration, fio: IO[A]): IO[A] = {
      if (count < 1) fio else fio.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times, fio)
        case Right(a) => IO(a)
      }
    }
    val split = 5
    inner(split, time / split, IO.fromFuture(IO(f))).unsafeToFuture()
  }

  case class TestContext(
    bakeryBoots: () => Future[Baker],
    remoteComponents: RemoteComponents,
    remoteInteraction: RemoteInteraction,
    remoteEventListener: RemoteEventListener,
    kubeApiServer: KubeApiServer
  )

  // Core dependencies
  def test(specText: String, testTags: Tag*)(runTest: TestContext => Future[Assertion])(implicit pos: source.Position): Unit = {

    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName, ConfigFactory.parseString("""akka.loglevel = "OFF" """))
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption

    it(specText, testTags: _*) {

      for {
        // Build mocks
        (mock, mocksPort) <- withOpenPort(5000, port => Future(startClientAndServer(port)))
        remoteInteraction = new RemoteInteraction(mock, Interactions.ReserveItemsInteraction)
        remoteEventListener = new RemoteEventListener(mock)
        kubeApiServer = new KubeApiServer(mock)
        remoteComponents = new RemoteComponents(kubeApiServer, remoteInteraction, remoteEventListener)

        // Build the bakery ecosystem
        serverBindingPromise: Promise[ServerBinding] = Promise()
        startBakery = () => {
          val kubernetesApi = new ApiClient().setBasePath(s"http://localhost:$mocksPort")
          val kubernetes = new ServiceDiscoveryKubernetes("default", kubernetesApi)
          val interactionManager = new InteractionsServiceDiscovery(kubernetes)
          val stateNodeBaker = AkkaBaker.withConfig(
            AkkaBakerConfig.localDefault(system).copy(
              interactionManager = interactionManager,
              bakerValidationSettings = AkkaBakerConfig.BakerValidationSettings(
                allowAddingRecipeWithoutRequiringInstances = true)))
          val eventListeners = new EventListenersServiceDiscovery(kubernetes, stateNodeBaker)
          withOpenPort(5010, port => StateNodeHttp.run(eventListeners, stateNodeBaker, "0.0.0.0", port)).map {
            case (serverBinding, serverPort) =>
              serverBindingPromise.complete(Success(serverBinding))
              BakerClient(Uri(s"http://localhost:$serverPort"))
          }
        }

        // Run the test
        assertionOrError <- runTest(TestContext(
          startBakery,
          remoteComponents,
          remoteInteraction,
          remoteEventListener,
          kubeApiServer
        )).transform(Success(_))

        // Clean
        serverBinding <- serverBindingPromise.future
        _ <- serverBinding.unbind()
        _ <- system.terminate()
        _ <- system.whenTerminated
        _ = mock.stop()
        assertion <- Future.fromTry(assertionOrError)
      } yield assertion
    }
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T]): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> (_, port)).recoverWith {
          case _: java.net.BindException => search(tail)
          case _: ChannelException => search(tail)
          case other =>
            println("REVIEW withOpenPort function implementation, uncaught exception: " +
              Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
