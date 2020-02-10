package com.ing.baker.baas.state

import java.util.UUID

import akka.actor.ActorSystem
import akka.http.scaladsl.model.Uri
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.implicits._
import com.ing.baker.baas.kubeapi
import com.ing.baker.baas.protocol.InteractionSchedulingProto._
import com.ing.baker.baas.protocol.ProtocolInteractionExecution
import com.ing.baker.baas.recipe.Events.{ItemsReserved, OrderPlaced}
import com.ing.baker.baas.recipe.Ingredients.{Item, OrderId, ReservedItems}
import com.ing.baker.baas.recipe.{Interactions, ItemReservationRecipe}
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.baas.state.StateNodeSpec._
import com.ing.baker.recipe.scaladsl.Interaction
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.common.{BakerException, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.EventInstance
import com.ing.baker.runtime.serialization.{Encryption, ProtoMap, SerializersProvider}
import io.kubernetes.client.openapi.ApiClient
import org.jboss.netty.channel.ChannelException
import org.mockserver.integration.ClientAndServer
import org.mockserver.integration.ClientAndServer.startClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.{HttpRequest, MediaType}
import org.scalatest.compatible.Assertion
import org.scalatest.{AsyncFlatSpec, BeforeAndAfterAll, Matchers}

import scala.concurrent.duration._
import scala.concurrent.{ExecutionContext, Future, Promise}
import scala.util.Success

class StateNodeSpec extends AsyncFlatSpec with BeforeAndAfterAll with Matchers {

  "The State Node" should "do recipe management" in {
    test ( context =>
      for {
        _ <- context.kubeApiServer.willRespondWithInteractionServices
        _ <- context.remoteInteraction.willPublishItsInterface
      } yield ()
    )( ( context, client ) =>
      for {
        recipeId <- client.addRecipe(ItemReservationRecipe.compiledRecipe)
        recipeInformation <- client.getRecipe(recipeId)
        noSuchRecipeError <- client
          .getRecipe("non-existent")
          .map(_ => None)
          .recover { case e: BakerException => Some(e) }
        allRecipes <- client.getAllRecipes
      } yield {
        recipeInformation.compiledRecipe shouldBe ItemReservationRecipe.compiledRecipe
        noSuchRecipeError shouldBe Some(BakerException.NoSuchRecipeException("non-existent"))
        allRecipes.get(recipeId).map(_.compiledRecipe) shouldBe Some(ItemReservationRecipe.compiledRecipe)
      }
    )
  }

  /***
   * TODO FIX THIS
   *
   * [MockServer-EventLog660] INFO org.mockserver.log.MockServerEventLog - request sequence not found, expected:
   *
   * [{
   * "method" : "GET",
   * "path" : "/api/v3/apply",
   * "headers" : {
   * "X-Bakery-Intent" : [ "Remote-Event-Listener:Webshop" ]
   * }
   * }]
   *
   * but was:
   *
   * [{
   * "method" : "GET",
   * "path" : "/api/v1/namespaces/default/services",
   * "headers" : {
   * "Accept" : [ "application/json" ],
   * "Content-Type" : [ "application/json" ],
   * "User-Agent" : [ "OpenAPI-Generator/1.0-SNAPSHOT/java" ],
   * "Host" : [ "localhost:5000" ],
   * "Connection" : [ "Keep-Alive" ],
   * "Accept-Encoding" : [ "gzip" ],
   * "content-length" : [ "0" ]
   * },
   * "keepAlive" : true,
   * "secure" : false
   * }, {
   * "method" : "GET",
   * "path" : "/api/v3/interface",
   * "headers" : {
   * "Host" : [ "localhost:5000" ],
   * "X-Bakery-Intent" : [ "Remote-Interaction:localhost" ],
   * "User-Agent" : [ "akka-http/10.1.11" ],
   * "content-length" : [ "0" ]
   * },
   * "keepAlive" : true,
   * "secure" : false
   * }, {
   * "method" : "POST",
   * "path" : "/api/v3/apply",
   * "headers" : {
   * "Host" : [ "localhost:5000" ],
   * "X-Bakery-Intent" : [ "Remote-Interaction:localhost" ],
   * "User-Agent" : [ "akka-http/10.1.11" ],
   * "Content-Type" : [ "application/octet-stream" ],
   * "Content-Length" : [ "77" ]
   * },
   * "keepAlive" : true,
   * "secure" : false,
   * "body" : {
   * "contentType" : "application/octet-stream",
   * "type" : "BINARY",
   * "base64Bytes" : "CiQKB29yZGVySWQaGZIDFgoUCgdvcmRlcklkEglSB29yZGVyLTEKJQoFaXRlbXMaHJoDGQoXkgMUChIKBml0ZW1JZBIIUgZpdGVtLTE="
   * }
   * }]
   */
  it should "bake" in {
    test ( context =>
      for {
        _ <- context.kubeApiServer.willRespondWithInteractionAndEventListenerServices
        _ <- context.remoteInteraction.willPublishItsInterface
      } yield ()
    )( ( context, client ) =>
      for {
        recipeId <- client.addRecipe(ItemReservationRecipe.compiledRecipe)

        event = OrderPlaced(orderId = OrderId("order-1"), items = List(Item("item-1")))
        eventInstance = EventInstance.unsafeFrom(event)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- context.remoteInteraction.willCallApply(event.items)
        _ <- context.remoteEventListener.willReceiveEvents

        _ <- client.bake(recipeId, recipeInstanceId)
        state <- client.getRecipeInstanceState(recipeInstanceId)
        _ = state.recipeInstanceId shouldBe recipeInstanceId

        status <- client.fireEventAndResolveWhenCompleted(recipeInstanceId, eventInstance)
        _ = status.sensoryEventStatus shouldBe SensoryEventStatus.Completed
        _ = status.eventNames should contain("OrderPlaced")
        _ = status.eventNames should contain("ItemsReserved")

        _ <- context.withRetry(times = 4, delay = 100.millis, context.remoteEventListener.verifyEventReceived)
      } yield succeed
    )
  }
}

object StateNodeSpec {

  private type ProtoMessage[A] = scalapb.GeneratedMessage with scalapb.Message[A]

  private def serialize[A, P <: ProtoMessage[P]](message: A)(implicit mapping: ProtoMap[A, P]): Array[Byte] =
    mapping.toByteArray(message)

  private implicit def serializersProvider(implicit system: ActorSystem, encryption: Encryption): SerializersProvider =
    SerializersProvider(system, encryption)

  class KubeApiServer()(implicit mock: ClientAndServer, ec: ExecutionContext) {

    def willRespondWithInteractionServices: Future[Unit] =
      willRespondWith(interactionServices)

    def willRespondWithInteractionAndEventListenerServices: Future[Unit] =
      willRespondWith(interactionAndEventListenersServices)

    def willRespondWith(services: kubeapi.Services): Future[Unit] = Future {
      mock.when(
        request()
          .withMethod("GET")
          .withPath("/api/v1/namespaces/default/services")
      ).respond(
        response()
          .withStatusCode(200)
          .withBody(services.mock, MediaType.APPLICATION_JSON)
      )
    }

    private def mockPort: kubeapi.PodPort =
      kubeapi.PodPort(
        name = "http-api",
        port = mock.getLocalPort,
        targetPort = Left(mock.getLocalPort))

    private def interactionServices: kubeapi.Services =
      kubeapi.Services(List(
        kubeapi.Service(
          metadata_name = "localhost",
          metadata_labels = Map("baas-component" -> "remote-interaction"),
          spec_ports = List(mockPort))
        )
      )

    private def interactionAndEventListenersServices: kubeapi.Services =
      interactionServices.++(kubeapi.Service(
        metadata_name = "localhost",
        metadata_labels = Map(
          "baas-component" -> "remote-event-listener",
          "baker-recipe" -> ItemReservationRecipe.compiledRecipe.name
        ),
        spec_ports = List(mockPort)
      ))
  }

  class RemoteInteraction(interaction: Interaction)(implicit mock: ClientAndServer, system: ActorSystem, encryption: Encryption) {

    import system.dispatcher

    def willPublishItsInterface: Future[Unit] = Future {
      mock.when(
        request()
          .withMethod("GET")
          .withPath("/api/v3/interface")
          .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
      ).respond(
        response()
          .withStatusCode(200)
          .withBody(serialize(ProtocolInteractionExecution.InstanceInterface(interaction.name, interaction.inputIngredients.map(_.ingredientType))))
      )
    }

    def willCallApply(items: List[Item]): Future[Unit] = Future {
      val event =
        EventInstance.unsafeFrom(ItemsReserved(ReservedItems(items, Array.fill(1)(Byte.MaxValue))))
      mock.when(
        request()
          .withMethod("POST")
          .withPath("/api/v3/apply")
          .withHeader("X-Bakery-Intent", s"Remote-Interaction:localhost")
      ).respond(
        response()
          .withStatusCode(200)
          .withBody(serialize(ProtocolInteractionExecution.InstanceExecutedSuccessfully(Some(event))))
      )
    }
  }

  class RemoteEventListener(ofRecipe: String)(implicit mock: ClientAndServer, system: ActorSystem, encryption: Encryption) {

    import system.dispatcher

    val eventApply: HttpRequest =
      request()
        .withMethod("GET")
        .withPath("/api/v3/apply")
        .withHeader("X-Bakery-Intent", s"Remote-Event-Listener:$ofRecipe")

    def willReceiveEvents: Future[Unit] = Future {
      mock.when(eventApply).respond(
        response()
          .withStatusCode(200)
      )
    }

    def verifyEventReceived: Future[Unit] = Future {
      mock.verify(eventApply)
    }
  }

  case class TestContext(
    remoteInteraction: RemoteInteraction,
    remoteEventListener: RemoteEventListener,
    kubeApiServer: KubeApiServer,
    system: ActorSystem
  ) {

    import system.dispatcher

    def wait(time: FiniteDuration): Future[Unit] = {
      val promise: Promise[Unit] = Promise()
      system.scheduler.scheduleOnce(time)(promise.complete(Success(())))
      promise.future
    }

    def withRetry[A](times: Int, delay: FiniteDuration, future: => Future[A]): Future[A] =
      future.recoverWith { case e =>
        if(times < 1) Future.failed(e)
        else wait(delay).flatMap(_ => withRetry(times - 1, delay, future))
      }
  }

  // Core dependencies
  def test(setup: TestContext => Future[Unit])(runTest: (TestContext, BakerClient) => Future[Assertion])(implicit ec: ExecutionContext): Future[Assertion] = {

    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption

    for {
      // Build mocks
      (mock, mocksPort) <- withOpenPort(5000, port => Future(startClientAndServer(port)))
      testContext = TestContext(
        remoteInteraction =
          new RemoteInteraction(Interactions.ReserveItemsInteraction)(mock, system, encryption),
        remoteEventListener =
          new RemoteEventListener(ItemReservationRecipe.compiledRecipe.name)(mock, system, encryption),
        kubeApiServer =
          new KubeApiServer()(mock, system.dispatcher),
        system =
          system
      )

      // Setup context
      _ <- setup(testContext)

      // Build the state node
      kubernetes = new ServiceDiscoveryKubernetes("default", new ApiClient().setBasePath(s"http://localhost:$mocksPort"))
      interactionManager = new InteractionsServiceDiscovery(kubernetes)
      stateNodeBaker = AkkaBaker.withConfig(AkkaBakerConfig.localDefault(system).copy(interactionManager = interactionManager))
      eventListeners = new EventListenersServiceDiscovery(kubernetes, stateNodeBaker)
      (binding, serverPort) <- withOpenPort(5010, port => StateNodeHttp.run(eventListeners, stateNodeBaker, "0.0.0.0", port))
      bakerClient = BakerClient(Uri(s"http://localhost:$serverPort"))

      // Run the test
      assertionOrError <- runTest(testContext, bakerClient).transform(Success(_))

      // Clean
      _ <- binding.unbind()
      _ <- system.terminate()
      _ <- system.whenTerminated
      _ = mock.stop()
      assertion <- Future.fromTry(assertionOrError)
    } yield assertion
  }

  private def withOpenPort[T](from: Int, f: Int => Future[T])(implicit ec: ExecutionContext): Future[(T, Int)] = {
    def search(ports: Stream[Int]): Future[(Stream[Int], (T, Int))] =
      ports match {
        case #::(port, tail) => f(port).map(tail -> (_, port)).recoverWith {
          case _: java.net.BindException => search(tail)
          case _: ChannelException => search(tail)
          case other => println("REVIEW withOpenPort function implementation, uncaught exception: " + Console.RED + other + Console.RESET); Future.failed(other)
        }
      }
    StateT(search).run(Stream.from(from, 1)).map(_._2)
  }
}
