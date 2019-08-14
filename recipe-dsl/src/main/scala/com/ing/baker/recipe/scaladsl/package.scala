package com.ing.baker.recipe

package object scaladsl {

  val processId: Ingredient[String] = new Ingredient[String](common.processIdName)
}


