package com.ing.baker.baas.state

import java.util.UUID

import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMethods, HttpRequest, Uri}
import akka.http.scaladsl.model.Uri.Path
import akka.http.scaladsl.unmarshalling.Unmarshal
import akka.stream.{ActorMaterializer, Materializer}
import cats.data.StateT
import cats.implicits._
import com.ing.baker.baas.scaladsl.BakerClient
import com.ing.baker.runtime.akka.{AkkaBaker, AkkaBakerConfig}
import com.ing.baker.runtime.serialization.Encryption
import com.typesafe.config.ConfigFactory
import de.heikoseeberger.akkahttpcirce.ErrorAccumulatingCirceSupport
import io.circe.Json
import io.circe.generic.auto._
import io.kubernetes.client.openapi.ApiClient
import org.jboss.netty.channel.ChannelException
import org.mockserver.client.MockServerClient
import org.mockserver.integration.ClientAndServer
import org.mockserver.integration.ClientAndServer.startClientAndServer
import org.mockserver.model.HttpRequest.request
import org.mockserver.model.HttpResponse.response
import org.mockserver.model.MediaType
import org.mockserver.model.Header.header
import org.mockserver.model.BodyWithContentType
import org.scalatest.compatible.Assertion
import org.scalatest.{AsyncFlatSpec, BeforeAndAfterAll, Matchers}

import scala.concurrent.duration._
import scala.concurrent.{Await, ExecutionContext, Future}
import StateNodeSpec._
import com.ing.baker.baas.recipe.CheckoutFlowRecipe
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe

class StateNodeSpec extends AsyncFlatSpec with BeforeAndAfterAll with Matchers {

  val compiledRecipe: CompiledRecipe = RecipeCompiler.compileRecipe(CheckoutFlowRecipe.recipe)

  "The State Node" should "add a recipe" in {
    test { implicit mock => client =>
      for {
        _ <- setup
        recipeId <- client.addRecipe(compiledRecipe)
        recipeInformation <- client.getRecipe(recipeId)
      } yield recipeInformation.compiledRecipe shouldBe compiledRecipe
    }

    /*
    case class Hello(hello: String)

    for {
      mock <- mockF
      _ = println(mock.getLocalPort)
      r = HttpRequest(method = HttpMethods.GET, uri = Uri(s"http://localhost:${mock.getLocalPort}/").withPath(Path./("test-path")))//, entity = encoded)
      //encoded <- Marshal(ProtocolDistributedEventPublishing.Event(recipeEventMetadata, event)).to[MessageEntity]
      response <- Http().singleRequest(r)
      decoded <- Unmarshal(response).to[Hello]
      _ = println(decoded)
    } yield succeed
     */
  }

  it should "other" in {
    ???
  }
}

object StateNodeSpec {

  private def getServicesResponse(implicit mock: ClientAndServer): String =
    s"""
      |{
      |  "kind": "ServiceList",
      |  "apiVersion": "v1",
      |  "metadata": {
      |    "selfLink": "/api/v1/namespaces/default/services",
      |    "resourceVersion": "67072"
      |  },
      |  "items": [
      |    {
      |      "metadata": {
      |        "name": "localhost",
      |        "namespace": "default",
      |        "selfLink": "/api/v1/namespaces/default/services/baas-event-listener-service",
      |        "uid": "1a4aeac2-e7ad-4318-8918-241b2a43512b",
      |        "resourceVersion": "35012",
      |        "creationTimestamp": "2020-02-04T15:09:09Z",
      |        "labels": {
      |          "baas-component": "remote-event-listener",
      |          "baker-recipe": "Webshop"
      |        }
      |      },
      |      "spec": {
      |        "ports": [
      |          {
      |            "name": "http-api",
      |            "protocol": "TCP",
      |            "port": ${mock.getLocalPort},
      |            "targetPort": "http-api"
      |          }
      |        ],
      |        "selector": {
      |          "app": "baas-event-listener"
      |        },
      |        "clusterIP": "10.110.209.3",
      |        "type": "ClusterIP",
      |        "sessionAffinity": "None"
      |      },
      |      "status": {
      |        "loadBalancer": {
      |
      |        }
      |      }
      |    },
      |    {
      |      "metadata": {
      |        "name": "localhost",
      |        "namespace": "default",
      |        "selfLink": "/api/v1/namespaces/default/services/reserve-items-interaction-service",
      |        "uid": "0470cdc2-f0aa-43b1-b9cd-b28017794001",
      |        "resourceVersion": "34969",
      |        "creationTimestamp": "2020-02-04T15:09:09Z",
      |        "labels": {
      |          "baas-component": "remote-interaction",
      |          "run": "reserve-items-interaction-service"
      |        }
      |      },
      |      "spec": {
      |        "ports": [
      |          {
      |            "name": "http-api",
      |            "protocol": "TCP",
      |            "port": ${mock.getLocalPort},
      |            "targetPort": "http-api"
      |          }
      |        ],
      |        "selector": {
      |          "app": "reserve-items"
      |        },
      |        "clusterIP": "10.109.106.112",
      |        "type": "ClusterIP",
      |        "sessionAffinity": "None"
      |      },
      |      "status": {
      |        "loadBalancer": {
      |
      |        }
      |      }
      |    }
      |  ]
      |}
      |""".stripMargin

  def setup(implicit mock: ClientAndServer, ec: ExecutionContext): Future[Unit] = Future {
    mock.when(
      request()
        .withMethod("GET")
        .withPath("/api/v1/namespaces/default/services")
    ).respond(
      response()
        .withStatusCode(200)
        .withBody(getServicesResponse, MediaType.APPLICATION_JSON)
    )
  }

  // Core dependencies
  def test(runTest: ClientAndServer => BakerClient => Future[Assertion])(implicit ec: ExecutionContext): Future[Assertion] = {
    val testId: UUID = UUID.randomUUID()
    val systemName: String = "baas-node-interaction-test-" + testId
    implicit val system: ActorSystem = ActorSystem(systemName)
    implicit val materializer: Materializer = ActorMaterializer()
    implicit val encryption: Encryption = Encryption.NoEncryption

    for {
      (mock, mocksPort) <- withOpenPort(5000, port => Future.successful(startClientAndServer(port)))
      kubernetes = new ServiceDiscoveryKubernetes("default", new ApiClient().setBasePath(s"http://localhost:$mocksPort"))
      interactionManager = new InteractionsServiceDiscovery(kubernetes)
      stateNodeBaker = AkkaBaker.withConfig(AkkaBakerConfig.localDefault(system).copy(interactionManager = interactionManager))
      eventListeners = new EventListenersServiceDiscovery(kubernetes, stateNodeBaker)
      (binding, serverPort) <- withOpenPort(5010, port => StateNodeHttp.run(eventListeners, stateNodeBaker, "0.0.0.0", port))
      assertion <- runTest(mock)(BakerClient(Uri(s"http://localhost:$serverPort")))
      _ <- binding.unbind()
      _ = mock.stop()
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
