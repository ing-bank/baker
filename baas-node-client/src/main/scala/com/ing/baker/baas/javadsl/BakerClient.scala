package com.ing.baker.baas.javadsl

import java.util.concurrent.{CompletableFuture, Executors}

import cats.effect.IO
import com.ing.baker.baas.scaladsl
import com.ing.baker.runtime.javadsl.{Baker => JavaBaker}
import org.http4s.Uri
import org.http4s.client.blaze.BlazeClientBuilder

import scala.compat.java8.FutureConverters
import scala.concurrent.{ExecutionContext, ExecutionContextExecutor}

object BakerClient {

  //TODO add resource cleanup possibility.
  def build(hostname: String): CompletableFuture[JavaBaker] = {
    val connectionPool: ExecutionContextExecutor =
      ExecutionContext.fromExecutor(Executors.newCachedThreadPool())

    implicit val ec = ExecutionContext.Implicits.global
    implicit val contextShift = IO.contextShift(ec)
    implicit val timer = IO.timer(ec)

    val future = BlazeClientBuilder[IO](connectionPool)
      .resource
      .map(new scaladsl.BakerClient(_, Uri.unsafeFromString(hostname)))
      .allocated
      .map{
        case (client, _) => new JavaBaker(client)
      }.unsafeToFuture()

    FutureConverters.toJava(future).toCompletableFuture
  }
}
