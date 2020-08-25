package com.ing.baker.baas.javadsl

import java.util
import java.util.concurrent.{CompletableFuture, Executors}

import cats.effect.IO
import com.ing.baker.baas.common.TLSConfig
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.{Request, Uri}

import scala.collection.JavaConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object BakerClient {

  //TODO add resource cleanup possibility.
  def build(hostname: String, filters: java.util.List[java.util.function.Function[Request[IO], Request[IO]]], tlsConfig: java.util.Optional[TLSConfig]): CompletableFuture[JavaBaker] = {
    val connectionPool: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    implicit val ec = ExecutionContext.Implicits.global
    implicit val contextShift = IO.contextShift(ec)
    implicit val timer = IO.timer(ec)

    val future = BlazeClientBuilder[IO](connectionPool, Option.apply(tlsConfig.orElse(null)).map(_.loadSSLContext))
      .resource
      .map(client => new scaladsl.BakerClient(client, Uri.unsafeFromString(hostname), filters.asScala.map(javaFun => req => javaFun.apply(req))))
      .allocated
      .map{
        case (client, _) => new JavaBaker(client)
      }.unsafeToFuture()

    FutureConverters.toJava(future).toCompletableFuture
  }

  def build(hostname: String, filters: java.util.List[java.util.function.Function[Request[IO], Request[IO]]]): CompletableFuture[JavaBaker] = {
    build(hostname, filters, java.util.Optional.empty())
  }

  def build(hostname: String, tlsConfig: java.util.Optional[TLSConfig]): CompletableFuture[JavaBaker] = {
    build(hostname, new util.ArrayList[java.util.function.Function[Request[IO], Request[IO]]](), tlsConfig)
  }

  def build(hostname: String): CompletableFuture[JavaBaker] = {
    build(hostname, new util.ArrayList[java.util.function.Function[Request[IO], Request[IO]]](), java.util.Optional.empty())
  }
}
