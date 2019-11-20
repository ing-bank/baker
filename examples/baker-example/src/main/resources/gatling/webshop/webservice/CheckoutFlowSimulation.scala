package webshop.webservice

import scala.concurrent.duration._

import io.gatling.core.Predef._
import io.gatling.http.Predef._
import io.gatling.jdbc.Predef._

class CheckoutFlowSimulation extends Simulation {

	val httpProtocol = http
		.baseUrl("http://localhost:8080")
		.inferHtmlResources()
		.acceptHeader("*/*")
		.acceptEncodingHeader("gzip, deflate")

	val scn = scenario("CheckoutFlowSimulation")
		.exec(http("Create Order")
			.post("/api/order")
			.header(HttpHeaderNames.ContentType, HttpHeaderValues.ApplicationJson)
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson)
			.body(StringBody("""{"items": ["item1", "item2"]}"""))
			.check(jsonPath("$..orderId").ofType[String].saveAs("orderId")))
		.pause(8)

		.exec(http("Check Status 1")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))
		.pause(6)

		.exec(http("Add Address")
			.put("/api/order/${orderId}/address")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson)
			.body(StringBody("""{"address": "Some Address #16"}""")))
		.pause(4)

		.exec(http("Check Status 2")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))
		.pause(16)

		.exec(http("Add Payment Information")
			.put("/api/order/${orderId}/payment")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson)
			.body(StringBody("""{"payment": "VISA 0000 0000 0000 0000"}""")))
		.pause(3)

		.exec(http("Poll Payment Outcome 1")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))
		.pause(1)

		.exec(http("Poll Payment Outcome 2")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))
		.pause(1)

		.exec(http("Poll Payment Outcome 3")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))
		.pause(1)

		.exec(http("Poll Payment Outcome 4")
			.get("/api/order/${orderId}")
  			.header(HttpHeaderNames.Accept, HttpHeaderValues.ApplicationJson))

	setUp(scn.inject(constantUsersPerSec(1) during (180 minutes))).protocols(httpProtocol)
}