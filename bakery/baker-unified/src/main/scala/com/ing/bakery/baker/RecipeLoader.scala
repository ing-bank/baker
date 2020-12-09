package com.ing.bakery.baker

import java.io.{ByteArrayInputStream, File, InputStream}
import java.nio.file.Files
import java.util.Base64
import java.util.zip.{GZIPInputStream, ZipException}

import cats.effect.{ContextShift, IO}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.ProtoMap
import com.typesafe.scalalogging.LazyLogging

import scala.util.Try

object RecipeLoader extends LazyLogging {

  def loadRecipesIntoBaker(path: String, baker: Baker)(implicit cs: ContextShift[IO]): IO[Unit] =
    for {
      recipes <- RecipeLoader.loadRecipes(path)
      _ <- IO{ if (recipes.isEmpty) logger.error(s"No recipes found in the recipe directory ($path), probably misconfiguration?")
          else logger.info(s"Recipes loaded: ${recipes.map(_.name)}") }
      _ <- recipes.traverse { recipe =>
        IO.fromFuture(IO(baker.addRecipe(recipe)))
      }
    } yield ()

  private[baker] def decode(bytes: Array[Byte]): Try[Array[Byte]] = Try {
    Base64.getDecoder.decode(new String(bytes))
  } recover {
    case _: IllegalArgumentException =>
      bytes
  }

  private[baker] def unzip(bytes: Array[Byte]): Try[Array[Byte]] = Try {
    val inputStream = new GZIPInputStream(new ByteArrayInputStream(bytes))
    Stream.continually(inputStream.read()).takeWhile(_ != -1).map(_.toByte).toArray
  } recover {
    case _: ZipException =>
      bytes
  }

  private[baker] def loadRecipes(path: String): IO[List[CompiledRecipe]] = {

    def recipeFiles(path: String): IO[List[File]] = IO {
      val d = new File(path)
      if (d.exists && d.isDirectory) {
        d
          .listFiles
          .filter(_.isFile)
          .filter(_.getName.endsWith(".recipe"))
          .toList
      } else {
        List.empty[File]
      }
    }

    for {
      files <- recipeFiles(path)
      recipes <- files.traverse(f => fromInputStream(Files.newInputStream(f.toPath)))
    } yield recipes
  }

  private def inputStreamToBytes(is: InputStream): Array[Byte] =
    Stream.continually(is.read).takeWhile(_ != -1).map(_.toByte).toArray

  def fromInputStream(inputStream: InputStream): IO[CompiledRecipe] = {
    for {
      rawBytes <- IO(inputStreamToBytes(inputStream))
      decodedBytes <- IO.fromTry(decode(rawBytes))
      payload <- IO.fromTry(unzip(decodedBytes))
      protoRecipe <- IO.fromTry(protobuf.CompiledRecipe.validate(payload))
      recipe <- IO.fromTry(ProtoMap.ctxFromProto(protoRecipe))
    } yield recipe
  }
}
