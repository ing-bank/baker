package examples.scala.application

import com.ing.baker.runtime.scaladsl.Baker

class ManualStopInteraction {
  def retryExample(baker: Baker, recipeInstanceId: String): Unit = {
    baker.stopRetryingInteraction(recipeInstanceId, "ShipOrder")
  }
}
