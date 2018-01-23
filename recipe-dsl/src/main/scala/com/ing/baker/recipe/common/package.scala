package com.ing.baker.recipe

import com.ing.baker.types.Type

package object common {

  type IngredientType = Type

  val ProcessIdName = "$ProcessId$"
  val SuccessEventAppend = "Successful"
  val exhaustedEventAppend = "RetryExhausted"

}
