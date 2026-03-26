package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common

import java.util
import scala.jdk.CollectionConverters._

case class CheckPointEvent(
                        nameInput: String = "",
                        requiredEventsInput: java.util.Set[String] = java.util.Set.of(),
                        requiredOneOfEventsInput: java.util.Set[java.util.Set[String]] = java.util.Set.of[java.util.Set[String]](java.util.Set.of[String]()))
  extends common.CheckPointEvent {
  override val name: String = nameInput
  override val requiredEvents: Set[String] = requiredEventsInput.asScala.toSet
  override val requiredOneOfEvents: Set[Set[String]] = requiredOneOfEventsInput.asScala.toSet.map((l: util.Set[String]) => l.asScala.toSet[String])
}
