package com.ing.baker.runtime.scaladsl

import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}

case class ProcessMetadata(recipeId: String, processId: String, createdTime: Long) extends common.ProcessMetadata with ScalaApi {

  def asJava: javadsl.ProcessMetadata =
    new javadsl.ProcessMetadata(recipeId, processId, createdTime)
}

