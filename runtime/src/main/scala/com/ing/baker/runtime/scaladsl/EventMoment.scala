package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.javadsl

case class EventMoment(name: String,
                       occurredOn: Long)
  extends common.EventMoment with ScalaApi {

  def asJava(): javadsl.EventMoment = javadsl.EventMoment(name, occurredOn)
}