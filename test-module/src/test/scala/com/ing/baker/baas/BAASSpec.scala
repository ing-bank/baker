package com.ing.baker.baas

import akka.http.scaladsl.Http
import akka.http.scaladsl.model.{HttpMessage, HttpRequest, HttpResponse, StatusCodes}
import akka.stream.ActorMaterializer
import akka.util.ByteString
import com.ing.baker.TestRecipeHelper
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.{commonserialize, scaladsl}

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}

class BAASSpec extends TestRecipeHelper {
  override def actorSystemName: String = "BAASSpec"

  "Serialize and deserialize a common recipe" in {
    val originalRecipe: commonserialize.Recipe = new commonserialize.Recipe(getComplexRecipe("name"))
    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)
    val deserializedRecipe = BAAS.deserializeRecipe(serializedRecipe)

    deserializedRecipe shouldBe originalRecipe
  }

  "Send recipe to the BAAS API" ignore {
    val originalRecipe: scaladsl.Recipe = getComplexRecipe("recipename")

    val serializedRecipe = BAAS.serializeRecipe(originalRecipe)

    implicit val materializer = ActorMaterializer()
    import defaultActorSystem.dispatcher

    val responseFuture: Future[HttpResponse] = Http()
      .singleRequest(HttpRequest(
        uri = "http://localhost:8081/recipe",
        method = akka.http.scaladsl.model.HttpMethods.POST,
        entity = ByteString.fromArray(serializedRecipe)))

    val returnMessage: HttpMessage = Await.result(responseFuture, 10 seconds)
    returnMessage match {
      case HttpResponse(StatusCodes.OK, headers, entity, _) =>
        entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
          println("Got response, body: " + body.utf8String)
        }
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
//        fail("Request failed, response code: " + code)
    }
  }
}
