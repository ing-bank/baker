package webshop.simple

import com.ing.baker.runtime.scaladsl.IngredientInstance
import com.ing.baker.types.{ListValue, PrimitiveValue}
import org.scalatest.flatspec.AsyncFlatSpec
import org.scalatest.matchers.should

import scala.collection.immutable.Seq

class SimpleInstancesSpec extends AsyncFlatSpec with should.Matchers {

  "Simple instances" should "be the same, whether created through reflection or not" in {
    val selfCreatedInstance = SimpleWebshopInstances.ReserveItemsInstance
    val reflectionInstance = SimpleWebshopInstancesReflection.reserveItemsInstance

    // Name and input should be the same
    selfCreatedInstance.name shouldEqual reflectionInstance.name
    selfCreatedInstance.input shouldEqual reflectionInstance.input

    val input = Seq(
      IngredientInstance("orderId", PrimitiveValue("o")),
      IngredientInstance("items", ListValue(List(PrimitiveValue("item1"))))
    )

    // the lambda should do the same
    for {
      r1 <- selfCreatedInstance.run(input)
      r2 <- reflectionInstance.run(input)
    } yield r1 shouldEqual r2

  }

}
