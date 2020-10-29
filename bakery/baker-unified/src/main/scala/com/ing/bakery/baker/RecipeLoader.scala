package com.ing.bakery.baker

import java.io.{ByteArrayInputStream, File}
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

  private def loadRecipes(path: String): IO[List[CompiledRecipe]] = {

    def extract(str: String): Try[Array[Byte]] = {
      val decodedBytes = Base64.getDecoder.decode(str)
      Try {
        val inputStream = new GZIPInputStream(new ByteArrayInputStream(decodedBytes))
        Stream.continually(inputStream.read()).takeWhile(_ != -1).map(_.toByte).toArray
      } recover {
        case _: ZipException =>
          decodedBytes
      }
    }

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
      recipes <- files.traverse { file =>
        for {
          string <- IO(new String(Files.readAllBytes(file.toPath)))
          payload <- IO.fromTry(extract(string))
          protoRecipe <- IO.fromTry(protobuf.CompiledRecipe.validate(payload))
          recipe <- IO.fromTry(ProtoMap.ctxFromProto(protoRecipe))
        } yield recipe
      }
    } yield recipes
  }
}
