package examples.scala.application

import com.ing.baker.runtime.scaladsl.Baker

class ManualRetryInteraction {
  def retryExample(baker: Baker, recipeInstanceId: String): Unit = {
    baker.retryInteraction(recipeInstanceId, "ShipOrder")
  }
}
