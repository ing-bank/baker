package com.ing.bakery.javadsl

import java.util
import java.util.concurrent.CompletableFuture
import java.util.concurrent.Executors.newCachedThreadPool
import java.util.{Optional, List => JList}

import cats.effect.{ContextShift, IO, Timer}
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}
import com.ing.bakery.common.TLSConfig
import com.ing.bakery.scaladsl
import org.http4s.client.blaze.BlazeClientBuilder
import org.http4s.{Request, Uri}

import scala.collection.JavaConverters._
import scala.compat.java8.FunctionConverters._
import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}


object BakerClient {
  type Filter = java.util.function.Function[Request[IO], Request[IO]]

  def build(hostname: String,
            filters: JList[Filter],
            tlsConfig: Optional[TLSConfig]): CompletableFuture[JavaBaker] = {
    build(List(hostname), filters, tlsConfig)
  }

  def build(hostname: String, filters: JList[Filter]): CompletableFuture[JavaBaker] = {
    build(hostname, filters, Optional.empty[TLSConfig]())
  }

  def build(hostname: String, tlsConfig: Optional[TLSConfig]): CompletableFuture[JavaBaker] = {
    build(hostname, util.Collections.emptyList[Filter](), tlsConfig)
  }

  def build(hostname: String): CompletableFuture[JavaBaker] = {
    build(hostname, util.Collections.emptyList[Filter](), Optional.empty[TLSConfig]())
  }

  //TODO add resource cleanup possibility.
  /**
    * Return async result with JavaBaker instance, using hosts, filters and tlsConfig
    *
    * @param hosts     List of hosts for baker cluster (more than 1 hosts is supported for multi-dc option)
    * @param filters   Http filters
    * @param tlsConfig TLS context for connection
    * @return JavaBaker
    */
  def build(hosts: List[String],
            filters: JList[Filter],
            tlsConfig: Optional[TLSConfig]): CompletableFuture[JavaBaker] = {

    val connectionPool: ExecutionContextExecutor = ExecutionContext.fromExecutor(newCachedThreadPool())
    val sslContext = if (tlsConfig.isPresent) Some(tlsConfig.get()).map(_.loadSSLContext) else None

    implicit val ec: ExecutionContext = ExecutionContext.Implicits.global
    implicit val contextShift: ContextShift[IO] = IO.contextShift(ec)
    implicit val timer: Timer[IO] = IO.timer(ec)

    val future = BlazeClientBuilder[IO](
      executionContext = connectionPool,
      sslContext = sslContext)
      .resource
      .map { client =>
        new scaladsl.BakerClient(
          client = client,
          hosts = hosts.map(Uri.unsafeFromString),
          filters = filters.asScala.map(_.asScala))
      }
      .allocated
      .map {
        case (client, _) => new JavaBaker(client)
      }
      .unsafeToFuture()

    FutureConverters.toJava(future).toCompletableFuture
  }
}