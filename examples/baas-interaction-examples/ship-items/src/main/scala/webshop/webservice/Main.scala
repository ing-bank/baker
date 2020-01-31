package webshop.webservice

import com.ing.baker.baas.scaladsl.RemoteInteraction
import com.ing.baker.runtime.scaladsl.InteractionInstance
import concurrent.ExecutionContext.Implicits.global

object Main extends App {
  RemoteInteraction.load(InteractionInstance.unsafeFrom(new ShipItemsInstance))
}