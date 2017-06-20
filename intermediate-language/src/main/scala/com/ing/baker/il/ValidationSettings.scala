package com.ing.baker.il

object ValidationSettings {
  val defaultValidationSettings = ValidationSettings()
}

/**
  *   Depending on the validations settings the following validations are done:
  *
  *   1. Check if all events and interactions are Java serializable
  *   2. Check if there are any cycles
  *   3. Check if there is any disconnectedness? (what is this?)
  *
  * @param allowCycles
  * @param allowDisconnectedness
  */
case class ValidationSettings(
    allowCycles: Boolean = true,
    allowDisconnectedness: Boolean = true
)
