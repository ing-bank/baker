package com.ing.bakery.baker

import java.io.{File, FileInputStream}
import java.nio.file.Files
import java.util.Base64

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.annotations.{FiresEvent, RecipeInstanceId, RequiresIngredient}
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.UntilDeadline
import com.ing.baker.recipe.javadsl.Interaction
import com.ing.baker.recipe.scaladsl.{Event, Recipe}
import com.ing.baker.runtime.common.Utils
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import scala.concurrent.duration._

class RecipeLoaderSpec extends AnyFunSuite with Matchers with BeforeAndAfterAll {

  private val plainRecipeFile = File.createTempFile("tmp", "recipe-plain")
  private val gzippedRecipeFile = File.createTempFile("tmp", "recipe-gzipped")
  private val plainBase64RecipeFile = File.createTempFile("tmp", "recipe-plain-base64")
  private val gzippedBase64RecipeFile = File.createTempFile("tmp", "recipe-gzipped-base64")

  override protected def beforeAll(): Unit = {
    val recipe: CompiledRecipe = RecipeCompiler.compileRecipe(Recipe("Webshop")
      .withSensoryEvents(
        Event[OrderPlaced],
        Event[PaymentMade])
      .withDefaultFailureStrategy(
        RetryWithIncrementalBackoff
          .builder()
          .withInitialDelay(100 milliseconds)
          .withUntil(Some(UntilDeadline(24 hours)))
          .withMaxTimeBetweenRetries(Some(10 minutes))
          .build()))

    val plainBytes = Utils.recipeToByteArray(recipe)
    val gzippedBytes = Utils.recipeToGZippedByteArray(recipe)

    Files.write(plainRecipeFile.toPath, plainBytes)
    Files.write(gzippedRecipeFile.toPath, gzippedBytes)
    Files.write(plainBase64RecipeFile.toPath, Base64.getEncoder.encode(plainBytes))
    Files.write(gzippedBase64RecipeFile.toPath, Base64.getEncoder.encode(gzippedBytes))
  }

  test("Recipes for tests are OK") {
    (for {
      r1 <- RecipeLoader.fromInputStream(getClass.getResourceAsStream("/recipes/ItemReservation.recipe"))
      r2 <- RecipeLoader.fromInputStream(getClass.getResourceAsStream("/recipes/ItemReservationBlocking.recipe"))
    } yield {
      assert(r1.name == "ItemReservation.recipe")
      assert(r2.name == "ItemReservation.recipe")
    }).unsafeRunSync()
  }

  test("Recipe loader from classpath") {
    (for {
      r <- RecipeLoader.loadRecipes(getClass.getResource("/recipes").getPath)
    } yield {
      assert(r.size == 2)
    }).unsafeRunSync()
  }

  test("GZipped then Base64ed recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(new FileInputStream(gzippedBase64RecipeFile))
    } yield {
      assert(recipe.name == "Webshop")
      ()
    }).unsafeRunSync()
  }

  test("GZipped recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(new FileInputStream(gzippedRecipeFile))
    } yield {
      assert(recipe.name == "Webshop")
      ()
    }).unsafeRunSync()
  }

  test("Plain Base64ed recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(new FileInputStream(plainBase64RecipeFile))
    } yield {
      assert(recipe.name == "Webshop")
      ()
    }).unsafeRunSync()
  }

  test("Plain recipe could be loaded") {
    (for {
      recipe <- RecipeLoader.fromInputStream(new FileInputStream(plainRecipeFile))
    } yield {
      assert(recipe.name == "Webshop")
      ()
    }).unsafeRunSync()
  }

  class CustomerInfo(val name: String, val address: String, val email: String) {}
  class OrderPlaced(val order: String) {}
  class CustomerInfoReceived(val customerInfo: CustomerInfo) {}

  object ValidateOrder {
    trait Outcome {}
    class Failed extends ValidateOrder.Outcome {}
    class Valid extends ValidateOrder.Outcome {}
  }

  trait ValidateOrder extends Interaction {
    @FiresEvent(oneOf = Array(classOf[ValidateOrder.Failed], classOf[ValidateOrder.Valid]))
    def apply(@RecipeInstanceId recipeInstanceId: String, @RequiresIngredient("order") key: String): ValidateOrder.Outcome
  }

  object ManufactureGoods {
    class GoodsManufactured(val goods: String) {}
  }

  trait ManufactureGoods extends Interaction {
    @FiresEvent(oneOf = Array(classOf[ManufactureGoods.GoodsManufactured]))
    def apply(@RequiresIngredient("order") order: String): ManufactureGoods.GoodsManufactured
  }

  object SendInvoice {
    class InvoiceWasSent {}
  }

  trait SendInvoice extends Interaction {
    @FiresEvent(oneOf = Array(classOf[SendInvoice.InvoiceWasSent]))
    def apply(@RequiresIngredient("customerInfo") customerInfo: CustomerInfo): SendInvoice.InvoiceWasSent
  }

  object ShipGoods {
    class GoodsShipped(val trackingId: String) {}
  }

  trait ShipGoods extends Interaction {
    @FiresEvent(oneOf = Array(classOf[ShipGoods.GoodsShipped]))
    def apply(@RequiresIngredient("goods") goods: String,
              @RequiresIngredient("customerInfo") customerInfo: CustomerInfo): ShipGoods.GoodsShipped
  }

  class PaymentMade {}

}

