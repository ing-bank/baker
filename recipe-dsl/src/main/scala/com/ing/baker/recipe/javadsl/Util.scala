package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common

object Util {
  /**
    * Creates the retry exhausted event name for the interaction the class represents.
    *
    * @param interactionClass
    * @return
    */
  def retryExhaustedEventName(interactionClass: Class[_]): String =
    interactionClass.getSimpleName + common.exhaustedEventAppend

  /**
    * Creates the retry exhausted event name for a interaction with this hame
    * This operation is usefull if you rename a operation
    *
    * @param interactionName the name of the interaction
    * @return
    */
  def retryExhaustedEventName(interactionName: String): String =
    interactionName + common.exhaustedEventAppend
}
