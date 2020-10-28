package com.ing.bakery.baker

import java.io.{ByteArrayInputStream, File}
import java.nio.file.Files
import java.util.Base64
import java.util.zip.{GZIPInputStream, ZipException}

import cats.effect.{ContextShift, IO, Timer}
import cats.implicits._
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.common.BakerException.NoSuchRecipeException
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.ProtoMap

import scala.util.Try

object RecipeLoader {

  def loadRecipesIntoBaker(path: String, baker: Baker)(implicit cs: ContextShift[IO]): IO[Unit] =
    for {
      recipes <- RecipeLoader.loadRecipes(path)
      _ <- if (recipes.isEmpty) IO.raiseError(new RuntimeException(s"No recipes found in the recipe directory ($path)")) else IO.unit
      _ <- recipes.traverse { recipe =>
        IO.fromFuture(IO(baker.addRecipe(recipe)))
      }
    } yield ()

  def loadRecipesIfRecipeNotFound[A](path: String, baker: Baker)(f: IO[A])(implicit timer: Timer[IO], cs: ContextShift[IO]): IO[A] = {
    f.attempt.flatMap {
      case Left(_: NoSuchRecipeException) => loadRecipesIntoBaker(path, baker) *> f
      case Left(e) => IO.raiseError(e)
      case Right(a) => IO.pure(a)
    }
  }

  def loadRecipes(path: String): IO[List[CompiledRecipe]] = {

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
