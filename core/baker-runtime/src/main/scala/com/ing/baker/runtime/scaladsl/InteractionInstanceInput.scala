package com.ing.baker.runtime.scaladsl

import java.util.Optional

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.Type

case class InteractionInstanceInput(name: Option[String], `type`: Type) extends common.InteractionInstanceInput with ScalaApi {
  def getName: Option[String] = name

  def getType: Type = `type`

  def asJava: javadsl.InteractionInstanceInput = javadsl.InteractionInstanceInput(Optional.ofNullable(name.orNull), `type`)

}
