package com.ing.baker.runtime.javadsl

import java.util.Optional

import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.types.Type

case class InteractionInstanceInput(name: Optional[String], `type`: Type) extends common.InteractionInstanceInput with JavaApi {
  def getName: Optional[String] = name

  def getType: Type = `type`

  def asScala: scaladsl.InteractionInstanceInput = scaladsl.InteractionInstanceInput(Option.apply(name.orElse(null)), `type`)

}
