package com.ing.baker

import java.util.UUID

import com.ing.baker.compiler.RecipeCompiler
import com.ing.baker.il.petrinet.InteractionTransition
import com.ing.baker.recipe.scaladsl._
import com.ing.baker.runtime.core.{Baker, ProcessState, RuntimeEvent}

import scala.concurrent.duration._

trait ScalaDSLRuntimeOps {
  implicit def toImplementations(seq: Seq[(String, ProcessState => RuntimeEvent)]): InteractionTransition[_] => (ProcessState => RuntimeEvent) = {
    val map = seq.toMap
    i => map(i.interactionName)
  }

  implicit class InteractionOps(i: Interaction) {

    // TODO use shapeless to abstract over function arity and add type safety

    val ingredientsFromProcessState = (procesState: ProcessState) => i.inputIngredients.map(_.name).map(procesState.ingredients)

    def implement[A](fn: A => RuntimeEvent): (String, ProcessState => RuntimeEvent) =
      i.name -> ingredientsFromProcessState.andThen(input => fn(input(0).asInstanceOf[A]))

    def implement[A, B](fn: (A, B) => RuntimeEvent): (String, ProcessState => RuntimeEvent) =
      i.name -> ingredientsFromProcessState.andThen(input => fn(input(0).asInstanceOf[A], input(1).asInstanceOf[B]))

    def implement[A, B, C](fn: (A, B, C) => RuntimeEvent): (String, ProcessState => RuntimeEvent) =
      i.name -> ingredientsFromProcessState.andThen(input => fn(input(0).asInstanceOf[A], input(1).asInstanceOf[B], input(2).asInstanceOf[C]))
  }

  implicit class EventOps(e: Event) {
    def instance(values: Any*): RuntimeEvent = {
      val ingredients = e.providedIngredients.map(_.name).zip(values.toSeq)
      RuntimeEvent(e.name, ingredients)
    }
  }
}

class ExamplesSpec extends TestRecipeHelper with ScalaDSLRuntimeOps {
  override def actorSystemName = "ExamplesSpec"

  "The example WebShop recipe" should {

    import WebShop._

    "compile without validation errors" in {

      // compiles the recipe
      val compiledRecipe = RecipeCompiler.compileRecipe(webShopRecipe)

      // prints any validation errors the compiler found
      compiledRecipe.validationErrors shouldBe empty
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
        (order: String) => valid.instance()
      }

      val manifactorGoodsImpl = manufactureGoods implement {
        (order: String) => goodsManufactured.instance(testGoods)
      }

      val sendInvoiceImpl = sendInvoice implement {
        (customerInfo: CustomerInfo) => invoiceWasSent.instance()
      }

      val shipGoodsImpl = shipGoods implement {
        (goods: String, customerInfo: CustomerInfo) => goodsShipped.instance(testTrackingId)
      }

      val implementations: InteractionTransition[_] => (ProcessState => RuntimeEvent) = Seq(validateOrderImpl, manifactorGoodsImpl, sendInvoiceImpl, shipGoodsImpl)

      val baker = new Baker(compiledRecipe, implementations)

      val processId = UUID.randomUUID().toString

      baker.bake(processId)

      implicit val timeout: FiniteDuration = 2 seconds

      // fire events

      baker.handleEvent(processId, orderPlaced.instance(testOrder))
      baker.handleEvent(processId, paymentMade.instance())
      baker.handleEvent(processId, customerInfoReceived.instance(testCustomerInfoData))

      val expectedIngredients = Map(
        "order" -> testOrder,
        "goods" -> testGoods,
        "customerInfo" -> testCustomerInfoData,
        "trackingId" -> testTrackingId)

      val actualIngredients = baker.getIngredients(processId)

      // assert the that all ingredients are provided
      actualIngredients shouldBe expectedIngredients

      // since events are eventually consistent we sleep here
      Thread.sleep(500)

      val expectedEvents = List(
        RuntimeEvent("OrderPlaced", Seq("order" -> testOrder)),
        RuntimeEvent("Valid", Seq.empty),
        RuntimeEvent("PaymentMade", Seq.empty),
        RuntimeEvent("GoodsManufactured", Seq("goods" -> testGoods)),
        RuntimeEvent("CustomerInfoReceived", Seq("customerInfo" -> testCustomerInfoData)),
        RuntimeEvent("GoodsShipped", Seq("trackingId" -> testTrackingId)),
        RuntimeEvent("InvoiceWasSent",Seq.empty))

      val actualEvents = baker.events(processId)

      actualEvents shouldBe expectedEvents
    }
  }
}
