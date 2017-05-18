package com.ing.baker.runtime.java_api

import java.time.Duration
import java.util.concurrent.{CompletableFuture, ExecutionException, TimeUnit, TimeoutException}
import java.util.{Map => JMap}

import com.ing.baker.runtime.core.NoSuchProcessException
import com.ing.baker.runtime.java_api.JBakerResponse._

import scala.compat.java8.FunctionConverters._
import scala.compat.java8.FutureConverters._
import scala.concurrent.Future

case class JBakerResponse(receiveAcknowledgement: CompletableFuture[Unit],
                          result: CompletableFuture[Unit]) {

  @throws(classOf[TimeoutException])
  @throws(classOf[NoSuchProcessException])
  def confirmReceived(duration: Duration): Unit = {
    try {
      receiveAcknowledgement.get(duration.toMillis, TimeUnit.MILLISECONDS)
    } catch {
      case e: ExecutionException => throw e.getCause
    }
  }

  @throws(classOf[TimeoutException])
  @throws(classOf[NoSuchProcessException])
  def confirmReceived: Unit = confirmReceived(defaultWaitTimeout)

  def confirmCompleted(duration: Duration): Unit =
    result.get(duration.toMillis, TimeUnit.MILLISECONDS)

  def confirmCompleted: Unit = confirmCompleted(defaultWaitTimeout)

  def onReceiveCompleted(
      fn: java.util.function.BiConsumer[Unit, Throwable]): JBakerResponse =
    this.copy(receiveAcknowledgement = receiveAcknowledgement.whenComplete(fn))
}

object JBakerResponse {

//  type BakerResult = JMap[String, AnyRef]

  val defaultWaitTimeout: Duration = Duration.ofSeconds(10)

  def apply(firstResponse: Future[Unit],
            lastResponse: Future[Unit]): JBakerResponse =
    JBakerResponse(scalaToJavaFuture(firstResponse), scalaToJavaFuture(lastResponse))

  def scalaToJavaFuture[S](sFuture: Future[S]): CompletableFuture[S] = {
    val completableFuture = new CompletableFuture[S]()
    val completionStage   = sFuture.toJava

    def extractResult(returnValue: S, throwable: Throwable): Unit =
      if (returnValue != null)
        completableFuture.complete(returnValue)
      else
        completableFuture.completeExceptionally(throwable)

    completionStage.whenComplete(asJavaBiConsumer(extractResult))
    completableFuture
  }
}
