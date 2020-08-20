package com.ing.baker.baas.javadsl

import java.util
import java.util.concurrent.{CompletableFuture, Executors}

import cats.effect.IO
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}
import org.http4s.{Request, Uri}
import org.http4s.client.blaze.BlazeClientBuilder

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object BakerClient {

  //TODO add resource cleanup possibility.
  def build(hostname: String, filters: java.util.List[Request[IO] => Request[IO]]): CompletableFuture[JavaBaker] = {
    val connectionPool: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    implicit val ec = ExecutionContext.Implicits.global
    implicit val contextShift = IO.contextShift(ec)
    implicit val timer = IO.timer(ec)

    val future = BlazeClientBuilder[IO](connectionPool)
      .resource
      .map(client => new scaladsl.BakerClient(client, Uri.unsafeFromString(hostname), filters.asScala))
      .allocated
      .map{
        case (client, _) => new JavaBaker(client)
      }.unsafeToFuture()

    FutureConverters.toJava(future).toCompletableFuture
  }

  def build(hostname: String): Unit = {
    build(hostname, new util.ArrayList[Request[IO] => Request[IO]]())
  }
}
