package com.ing.baker.baas.state

import java.io.File
import java.nio.file.Files

import cats.implicits._
import cats.effect.{ContextShift, IO}
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.akka.actor.protobuf
import com.ing.baker.runtime.scaladsl.Baker
import com.ing.baker.runtime.serialization.ProtoMap
import org.apache.commons.codec.binary.Base64

object RecipeLoader {

  def loadRecipesIntoBaker(path: String, baker: Baker)(implicit cs: ContextShift[IO]): IO[Unit] =
    for {
      recipes <- RecipeLoader.loadRecipes(path)
      _ <- if (recipes.isEmpty) IO.raiseError(new RuntimeException(s"No recipes found in the recipe directory ($path)")) else IO.unit
      _ <- recipes.traverse { recipe =>
        IO.fromFuture(IO(baker.addRecipe(recipe)))
      }
    } yield ()

  def loadRecipes(path: String): IO[List[CompiledRecipe]] = {

    def recipeFiles(path: String): IO[List[File]] = IO {
      val d = new File(path)
      if (d.exists && d.isDirectory) {
        d.listFiles.filter(_.isFile).toList
      } else {
        List.empty[File]
      }
    }

    for {
      files <- recipeFiles(path)
      recipes <- files.traverse { file =>
        for {
          bytes <- IO(Files.readAllBytes(file.toPath))
          decode64 = Base64.decodeBase64(new String(bytes))
          protoRecipe <- IO.fromTry(protobuf.CompiledRecipe.validate(decode64))
          recipe <- IO.fromTry(ProtoMap.ctxFromProto(protoRecipe))
        } yield recipe
      }
    } yield recipes
  }
}
