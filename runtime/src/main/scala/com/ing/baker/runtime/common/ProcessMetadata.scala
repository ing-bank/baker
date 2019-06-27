package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi

/**
  * This class holds some meta data of a baker process.
  */
trait ProcessMetadata extends LanguageApi {

  val recipeId: String

  val processId: String

  val createdTime: Long
}
