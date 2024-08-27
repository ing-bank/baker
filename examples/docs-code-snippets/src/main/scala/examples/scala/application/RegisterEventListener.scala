package examples.scala.application

import com.ing.baker.runtime.scaladsl.Baker

class RegisterEventListener(val baker: Baker) {

  def example(): Unit = {
    baker.registerEventListener((recipeInstanceId, event) =>
      println(s"Recipe instance: $recipeInstanceId, processed event: $event")
    )
  }
}
