package com.ing.baker.runtime.common

import com.ing.baker.runtime.common.LanguageDataStructures.LanguageApi
import com.ing.baker.types.Type


/**
  * The type that describe the input for InteractionInstances
  */
trait InteractionInstanceInput extends LanguageApi { self =>

  //This is an Option because in Java we cannot get the name from the variable using reflection
  val name: language.Option[String]

  val `type`: Type
}
