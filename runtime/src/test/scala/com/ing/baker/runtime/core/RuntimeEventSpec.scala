package com.ing.baker.runtime.core

import com.ing.baker.il.{EventType, IngredientType}
import org.scalatest.{FunSuite, Matchers}

class RuntimeEventSpec extends FunSuite with Matchers {

  test("empty RuntimeEvent has the correct EventType") {
    RuntimeEvent("name", Seq.empty).eventType shouldEqual EventType("name", Seq.empty)
  }

  test("RuntimeEvent with multiple ingredients has the correct EventType") {
    RuntimeEvent("name", Seq(
      "str1" -> "ingredientValue",
      "int1" -> 5,
      "long1" -> 9l
    )).eventType shouldEqual EventType("name", Seq(
      IngredientType("str1", classOf[String]),
      IngredientType("int1", classOf[java.lang.Integer]),
      IngredientType("long1", classOf[java.lang.Long])
    ))
  }

}
