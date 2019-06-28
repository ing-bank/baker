package com.ing.baker.baas.util

import akka.NotUsed
import akka.actor.ActorSystem
import akka.http.scaladsl.Http
import akka.http.scaladsl.marshalling.{Marshaller, PredefinedToEntityMarshallers}
import akka.http.scaladsl.model._
import akka.http.scaladsl.unmarshalling.{PredefinedFromEntityUnmarshallers, Unmarshaller}
import akka.serialization.{Serialization, SerializationExtension}
import akka.stream.scaladsl.Flow
import akka.stream.{ActorMaterializer, Materializer}
import akka.util.ByteString
import com.ing.baker.baas.interaction.server.protocol.{ExecuteInteractionHTTPRequest, ExecuteInteractionHTTPResponse}
import com.ing.baker.baas.server.protocol._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.{RecipeInformation, SensoryEventStatus}
import com.ing.baker.runtime.scaladsl.ProcessState
import com.ing.baker.runtime.scaladsl.EventInstance
import org.slf4j.LoggerFactory

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.FiniteDuration
import scala.concurrent.{Await, Future}
import scala.reflect.ClassTag

trait ClientUtils {

  implicit val actorSystem: ActorSystem
  implicit val serializer: Serialization = SerializationExtension.get(actorSystem)
  implicit val materializer = ActorMaterializer()

  val log = LoggerFactory.getLogger(this.getClass.getName)

  def serializeFlow[T <: AnyRef]: Flow[T, ByteString, NotUsed] =
    Flow.fromFunction(obj => ByteString(serializer.serialize(obj).get))

  def deserializeFlow[T](implicit ct: ClassTag[T]): Flow[ByteString, T, NotUsed] =
    Flow.fromFunction(string => serializer.deserialize(string.toArray, ct.runtimeClass).get.asInstanceOf[T])

  def entityFromResponse[T: ClassTag](entity: ResponseEntity)(implicit ct: ClassTag[T], materializer: Materializer, timeout: FiniteDuration): T = {
    val byteString = Await.result(entity.dataBytes.runFold(ByteString(""))(_ ++ _), timeout)
    serializer.deserialize(byteString.toArray, ct.runtimeClass).get.asInstanceOf[T]
  }

  def doRequestAndParseResponse[T: ClassTag](httpRequest: HttpRequest)(implicit actorSystem: ActorSystem, materializer: Materializer, timeout: FiniteDuration): Future[T] = {
    doRequest(httpRequest, e => entityFromResponse[T](e))
  }

  def doRequest[T](httpRequest: HttpRequest, fn: ResponseEntity => T)(implicit actorSystem: ActorSystem, materializer: Materializer, timeout: FiniteDuration): Future[T] = {

    log.info(s"Sending request: $httpRequest")

    val response: Future[HttpMessage] = Http().singleRequest(httpRequest)

    response map {
      case HttpResponse(StatusCodes.OK, _, entity, _) =>
        fn(entity)
      case resp @ HttpResponse(code, _, _, _) =>
        resp.discardEntityBytes()
        log.error("Request failed with response code: " + code)
        throw new RuntimeException("Request failed with response code: " + code)
    }
  }

  def logEntity = (entity: ResponseEntity) =>
    entity.dataBytes.runFold(ByteString(""))(_ ++ _).foreach { body =>
      log.info("Got response body: " + body.utf8String)
    }

  def akkaProtoUnmarshaller[T](implicit ct: ClassTag[T]): Unmarshaller[HttpEntity, T] =
    PredefinedFromEntityUnmarshallers.byteArrayUnmarshaller.map { string: Array[Byte] =>
      serializer.deserialize(string, ct.runtimeClass).get.asInstanceOf[T]
    }

  def akkaProtoMarshaller[T <: AnyRef]: Marshaller[T, MessageEntity] = PredefinedToEntityMarshallers.ByteArrayMarshaller.compose[T] { obj =>
    serializer.serialize(obj).get
  }

  implicit val processStateMarshaller = akkaProtoMarshaller[ProcessState]
  implicit val processStateUnmarshaller = akkaProtoUnmarshaller[ProcessState]

  implicit val executeInteractionHTTPRequestMarshaller = akkaProtoMarshaller[ExecuteInteractionHTTPRequest]
  implicit val executeInteractionHTTPRequestUnmarshaller = akkaProtoUnmarshaller[ExecuteInteractionHTTPRequest]

  implicit val executeInteractionHTTPResponseMarshaller = akkaProtoMarshaller[ExecuteInteractionHTTPResponse]
  implicit val executeInteractionHTTPResponseUnmarshaller = akkaProtoUnmarshaller[ExecuteInteractionHTTPResponse]

  implicit val eventMarshaller = akkaProtoMarshaller[EventInstance]
  implicit val eventUnmarshaller = akkaProtoUnmarshaller[EventInstance]

  implicit val compiledRecipeMarshaller = akkaProtoMarshaller[CompiledRecipe]
  implicit val compiledRecipeUnmarshaller = akkaProtoUnmarshaller[CompiledRecipe]

  implicit val recipeInformationMarshaller = akkaProtoMarshaller[RecipeInformation]
  implicit val recipeInformationUnmarshaller = akkaProtoUnmarshaller[RecipeInformation]

  implicit val sensoryEventStatusMarhaller = akkaProtoMarshaller[SensoryEventStatus]
  implicit val sensoryEventStatusUnmarshaller = akkaProtoUnmarshaller[SensoryEventStatus]

  implicit val processEventRequestMarshaller = akkaProtoMarshaller[ProcessEventRequest]
  implicit val processEventRequestUnMarshaller = akkaProtoUnmarshaller[ProcessEventRequest]

  implicit val processEventResponseMarshaller = akkaProtoMarshaller[ProcessEventResponse]
  implicit val processEventResponseUnMarshaller = akkaProtoUnmarshaller[ProcessEventResponse]

  implicit val addInteractionHTTPRequestMarshaller = akkaProtoMarshaller[AddInteractionHTTPRequest]
  implicit val addInteractionHTTPRequestUnMarshaller = akkaProtoUnmarshaller[AddInteractionHTTPRequest]

  implicit val addInteractionHTTPResponseMarshaller = akkaProtoMarshaller[AddInteractionHTTPResponse]
  implicit val addInteractionHTTPResponseUnMarshaller = akkaProtoUnmarshaller[AddInteractionHTTPResponse]

  implicit val eventsResponseMarshaller = akkaProtoMarshaller[EventsResponse]
  implicit val eventsResponseUnMarshaller = akkaProtoUnmarshaller[EventsResponse]

  implicit val stateResponseMarshaller = akkaProtoMarshaller[StateResponse]
  implicit val stateResponseUnMarshaller = akkaProtoUnmarshaller[StateResponse]

  implicit val bakeRequestMarshaller = akkaProtoMarshaller[BakeRequest]
  implicit val bakeRequestUnMarshaller = akkaProtoUnmarshaller[BakeRequest]

  implicit val bakeResponseMarshaller = akkaProtoMarshaller[BakeResponse]
  implicit val bakeResponseUnMarshaller = akkaProtoUnmarshaller[BakeResponse]

  implicit val ingredientsResponseMarshaller = akkaProtoMarshaller[IngredientsResponse]
  implicit val ingredientsResponseUnMarshaller = akkaProtoUnmarshaller[IngredientsResponse]

  implicit val visualStateResponseMarshaller = akkaProtoMarshaller[VisualStateResponse]
  implicit val visualStateResponseUnMarshaller = akkaProtoUnmarshaller[VisualStateResponse]

  implicit val addRecipeRequestMarshaller = akkaProtoMarshaller[AddRecipeRequest]
  implicit val addRecipeRequestUnMarshaller = akkaProtoUnmarshaller[AddRecipeRequest]

  implicit val addRecipeResponseMarshaller = akkaProtoMarshaller[AddRecipeResponse]
  implicit val addRecipeResponseUnMarshaller = akkaProtoUnmarshaller[AddRecipeResponse]
}
