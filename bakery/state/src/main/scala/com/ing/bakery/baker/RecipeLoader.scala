package com.ing.bakery.baker

import java.io.{ByteArrayInputStream, File, InputStream}
import java.nio.file.{Files, Path}
import java.util.Base64
import java.util.zip.{GZIPInputStream, ZipException}
import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.ProtoMap
import com.typesafe.scalalogging.LazyLogging

import scala.util.Try
import java.nio.file.Files
import java.nio.file.attribute.BasicFileAttributes
import scala.concurrent.duration.FiniteDuration

object RecipeLoader extends LazyLogging {

  def pollRecipesUpdates(path: String, recipeCache: RecipeCache, baker: Baker, duration: FiniteDuration)
                        (implicit timer: Timer[IO], cs: ContextShift[IO]): IO[Unit] = {
    def pollRecipes: IO[Unit] = loadRecipesIntoBaker(path, recipeCache, baker) >> IO.sleep(duration) >> IO.suspend(pollRecipes)

    pollRecipes
  }

  def loadRecipesIntoBaker(path: String, recipeCache: RecipeCache, baker: Baker)(implicit cs: ContextShift[IO]): IO[Unit] =
    for {
      newRecipes <- RecipeLoader.loadRecipes(path)
      recipes <- recipeCache.merge(newRecipes)
      _ <- IO{ if (recipes.isEmpty) logger.warn(s"No recipes found in the recipe directory $path or cache")
          else logger.debug(s"Recipes loaded: ${recipes.map(_.name)}") }
      _ <- recipes.traverse { record =>
        IO.fromFuture(IO(baker.addRecipe(record)))
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

  private[baker] def loadRecipes(path: String): IO[List[RecipeRecord]] = {

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
      recipes <- files.traverse(f => fromFile(f.toPath))
    } yield recipes.map { case (recipe, updated) =>
      RecipeRecord.of(recipe, updated)
    }
  }

  def fromFile(f: Path): IO[(CompiledRecipe, Long)] = {
    for {
      recipe <- fromBytes(inputStreamToBytes(Files.newInputStream(f)))
      updated <- IO(Files.readAttributes(f, classOf[BasicFileAttributes]).lastModifiedTime().toMillis)
    } yield {
      logger.info(s"${f.toFile.getName} -> ${recipe.name}:${recipe.recipeId}")
      (recipe, updated)
    }
  }

  private def inputStreamToBytes(is: InputStream): Array[Byte] =
    Stream.continually(is.read).takeWhile(_ != -1).map(_.toByte).toArray

  def fromBytes(rawBytes: Array[Byte]): IO[CompiledRecipe] = {
    for {
      decodedBytes <- IO.fromTry(decode(rawBytes))
      payload <- IO.fromTry(unzip(decodedBytes))
      protoRecipe <- IO.fromTry(protobuf.CompiledRecipe.validate(payload))
      recipe <- IO.fromTry(ProtoMap.ctxFromProto(protoRecipe))
    } yield recipe
  }
}
