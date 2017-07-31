package com.ing.baker.il

object ValidationSettings {
  val defaultValidationSettings = ValidationSettings()
}

/**
  * Depending on the validations settings the following validations are done:
  *
  *   1. Check if there are any cycles
  *   2. Check if there is any disconnectedness? (what is this?)
  *   3. Check if there exist any non-executable interaction or not
  *
  * @param allowCycles
  * @param allowDisconnectedness
  * @param allowNonExecutableInteractions
  */
case class ValidationSettings(allowCycles: Boolean = true,
                              allowDisconnectedness: Boolean = true,
                              allowNonExecutableInteractions: Boolean = true)
