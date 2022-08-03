package com.ing.baker.http.server.scaladsl

import cats.effect.testing.scalatest.AsyncIOSpec
import cats.effect.{Blocker, IO, Resource}
import com.ing.baker.http.DashboardConfiguration
import com.ing.baker.runtime.scaladsl.Baker
import io.prometheus.client.CollectorRegistry
import org.http4s.headers.{`Content-Length`, `Content-Type`}
import org.http4s.implicits._
import org.http4s.metrics.MetricsOps
import org.http4s.metrics.prometheus.Prometheus
import org.http4s._
import org.mockito.Mockito.{times, verify, when}
import org.mockito.MockitoSugar.mock
import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should.Matchers

import scala.concurrent.Future

class Http4sBBakerServerSpec  extends AsyncFlatSpec with AsyncIOSpec with Matchers{

  val bakerMock: Baker = mock[Baker]

  val dashboardConfigurationEnabled: DashboardConfiguration =
    DashboardConfiguration(enabled = true, applicationName = "TestCluster", clusterInformation = Map.empty)
  val dashboardConfigurationDisabled: DashboardConfiguration =
    dashboardConfigurationEnabled.copy(enabled = false)

  def check[A](actual: IO[Response[IO]],
               expectedStatus: Status,
               expectedBody: Option[A])(
                implicit ev: EntityDecoder[IO, A]
              ): Boolean = {
    val actualResp = actual.unsafeRunSync()
    val statusCheck = actualResp.status == expectedStatus
    val bodyCheck = expectedBody.fold[Boolean](
      // Verify Response's body is empty.
      actualResp.body.compile.toVector.unsafeRunSync().isEmpty)(
      expected => actualResp.as[A].unsafeRunSync() == expected
    )
    statusCheck && bodyCheck
  }

  private def routes(metrics: MetricsOps[IO],
                     blocker: Blocker,
                     dashboardConfiguration: DashboardConfiguration): HttpRoutes[IO] = Http4sBakerServer.routes(
    baker = bakerMock,
    apiUrlPrefix = "/api/test",
    metrics = metrics,
    dashboardConfiguration = dashboardConfiguration,
    blocker = blocker
  )

  private def doRequest(request : Request[IO],
                        dashboardConfiguration: DashboardConfiguration = dashboardConfigurationEnabled) : Response[IO] = {
    val routesResource: Resource[IO, HttpRoutes[IO]] = for {
      metrics <- Prometheus.metricsOps[IO](CollectorRegistry.defaultRegistry, "test")
      blocker <- Blocker[IO]
    } yield routes(metrics, blocker, dashboardConfiguration)

    routesResource.use(_.orNotFound.run(request)).unsafeRunSync()
  }

  "the routes" should "give 404 for non-existent urls" in {
    val response = doRequest(Request(method = Method.GET, uri = uri"/non-existent"))
    response.status shouldEqual Status.NotFound
  }

  "the routes" should "serve the dashboard index file if dashboard is enabled" in {
    val response = doRequest(Request(method = Method.GET, uri = uri"/"))
    response.status shouldEqual Status.Ok
    response.headers.get(`Content-Type`).toString shouldEqual "Some(Content-Type: text/html)"
  }

  "the routes" should "serve the other static files if dashboard is enabled" in {
    val response = doRequest(Request(method = Method.GET, uri = uri"/main.js"))
    response.status shouldEqual Status.Ok
    response.headers.get(`Content-Type`).toString shouldEqual "Some(Content-Type: application/javascript)"
  }

  "the routes" should "give 404 if dashboard is disabled" in {
    val response = doRequest(Request(method = Method.GET, uri = uri"/"), dashboardConfigurationDisabled)
    response.status shouldEqual Status.NotFound
  }

  "the routes" should "give dashboard_config" in {
    val response = doRequest(Request(method = Method.GET, uri = uri"/dashboard_config"))
    response.status shouldEqual Status.Ok
    response.headers.get(`Content-Length`).toString shouldEqual "Some(Content-Length: 104)"
  }

  "the routes" should "call the underlying baker implementation" in {
    when(bakerMock.getAllInteractions).thenReturn(Future.successful(List.empty))
    val response = doRequest(Request(method = Method.GET, uri = uri"/api/test/app/interactions"))
    verify(bakerMock, times(1)).getAllInteractions
    response.status shouldEqual Status.Ok
  }

}
