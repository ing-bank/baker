package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.runtime.{common, scaladsl}

case class EventMoment(name: String,
                       occurredOn: Long)
  extends common.EventMoment with JavaApi {

  def getName: String = name

  def getOccurredOn: Long = occurredOn

  def asScala: scaladsl.EventMoment = scaladsl.EventMoment(name, occurredOn)
}