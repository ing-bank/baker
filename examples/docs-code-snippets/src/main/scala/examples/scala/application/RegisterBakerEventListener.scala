package examples.scala.application

import com.ing.baker.runtime.scaladsl.Baker

class RegisterBakerEventListener(val baker: Baker) {

  def example(): Unit = {
    baker.registerBakerEventListener((bakerEvent) =>
      println(s"Received event: $bakerEvent")
    )
  }
}
