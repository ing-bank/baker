package examples.scala.application

import com.ing.baker.runtime.scaladsl.{Baker, EventInstance}

def resolveExample(baker: Baker, recipeInstanceId: String): Unit = {
  baker.resolveInteraction(
    recipeInstanceId,
    "ShipOrder",
    EventInstance("ShippingFailed")
  )
}
