package com.ing.bakery.baker

import java.io.{File, FileInputStream}
import java.nio.file.Files

import com.ing.baker.runtime.common.Utils
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

class RecipeLoaderSpec extends AnyFunSuite with Matchers {

  test("GZipped then Base64ed recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(this.getClass.getClassLoader.getResourceAsStream("gzipped_then_base64.recipe"))
    } yield {
      assert(recipe.name == "OpenChildAccountRecipe")
      ()
    }).unsafeRunSync()

  }

  test("GZipped recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(this.getClass.getClassLoader.getResourceAsStream("gzipped.recipe"))
    } yield {
      assert(recipe.name == "OpenChildAccountRecipe")
      ()
    }).unsafeRunSync()
  }

  test("Read recipe and save it back as zipped") {
    val file = File.createTempFile("tmp", "recipe")
    (for {
      plainRecipe <- RecipeLoader.fromInputStream(this.getClass.getClassLoader.getResourceAsStream("plain.recipe"))
      gzippedBytes = Utils.recipeToGZippedByteArray(plainRecipe)
      _ = Files.write(file.toPath, gzippedBytes)
      recipe <- RecipeLoader.fromInputStream(new FileInputStream(file))
    } yield {
      assert(recipe.name == "OpenChildAccountRecipe")
      ()
    }).unsafeRunSync()

  }

}

