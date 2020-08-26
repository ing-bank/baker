package com.ing.baker.runtime

import com.ing.baker.BakerRuntimeTestBase
import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.ScalaDSLRuntime._
import com.ing.baker.runtime.scaladsl.Baker
import com.typesafe.config.ConfigFactory
import java.util.UUID

import com.ing.baker.runtime.akka.AkkaBaker

import scala.concurrent.Future

class ExamplesSpec extends BakerRuntimeTestBase  {
  override def actorSystemName = "ExamplesSpec"

  "The WebShop recipe" should {
    import Examples.webshop._

    "compile without validation errors" in {

      // compiles the recipe
      val compiledRecipe = RecipeCompiler.compileRecipe(webShopRecipe)

//      println(s"Visual recipe: ${compiledRecipe.getRecipeVisualization}")

      // prints any validation errors the compiler found
      Future { compiledRecipe.validationErrors shouldBe empty }
    }

    "run a happy flow" in {

      // compiles the recipe
      val compiledRecipe = RecipeCompiler.compileRecipe(webShopRecipe)

      // test data
      val testCustomerInfoData = CustomerInfo("John Snow", "Winterfell", "john_snow@hotmail.com")
      val testOrder = "Valyrian steel sword"
      val testGoods = "Valyrian steel sword instance"
      val testTrackingId = "001"

      // create implementations of the interactions
      val validateOrderImpl = validateOrder implement {
        (order: String) => {
          // Some logic here
          valid.instance() // or maybe invalid event to be returned
        }
      }

      val manufactureGoodsImpl = manufactureGoods implement {
        order: String => {
          // Some logic here
          goodsManufactured.instance(testGoods)
        }
      }

      val sendInvoiceImpl = sendInvoice implement {
        customerInfo: CustomerInfo => invoiceWasSent.instance()
      }

      val shipGoodsImpl = shipGoods implement {
        (goods: String, customerInfo: CustomerInfo) => goodsShipped.instance(testTrackingId)
      }

      val implementations =
        Seq(validateOrderImpl, manufactureGoodsImpl, sendInvoiceImpl, shipGoodsImpl)

      val baker = AkkaBaker(ConfigFactory.load(), defaultActorSystem)

      for {
        _ <- Future.traverse(implementations)(baker.addInteractionInstance)
        recipeId <- baker.addRecipe(compiledRecipe)
        recipeInstanceId = UUID.randomUUID().toString
        _ <- baker.bake(recipeId, recipeInstanceId)
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, orderPlaced.instance(testOrder))
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, paymentMade.instance())
        _ <- baker.fireEventAndResolveWhenCompleted(recipeInstanceId, customerInfoReceived.instance(testCustomerInfoData))
        expectedIngredients = IngredientMap(
          order -> testOrder,
          goods -> testGoods,
          customerInfo -> testCustomerInfoData,
          trackingId -> testTrackingId)
        state <- baker.getRecipeInstanceState(recipeInstanceId)
        // assert the that all ingredients are provided
        _ = state.ingredients shouldBe expectedIngredients
        expectedEvents = List(
          orderPlaced.instance(testOrder),
          valid.instance(),
          paymentMade.instance(),
          goodsManufactured.instance(testGoods),
          customerInfoReceived.instance(testCustomerInfoData),
          goodsShipped.instance(testTrackingId),
          invoiceWasSent.instance())
        _ = state.eventNames shouldBe expectedEvents.map(_.name)
      } yield succeed
    }
  }

  "The open account recipe" should {

    import Examples.open_account._

    "compile without validation errors" in {

      // compiles the recipe
      val compiledRecipe = RecipeCompiler.compileRecipe(openAccountRecipe)

      // prints any validation errors the compiler found
      Future { compiledRecipe.validationErrors shouldBe empty }
    }
  }
}
