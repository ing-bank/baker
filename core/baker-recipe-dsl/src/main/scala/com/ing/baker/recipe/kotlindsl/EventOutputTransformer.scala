package com.ing.baker.recipe.kotlindsl

import com.ing.baker.recipe.common

import scala.jdk.CollectionConverters._

import scala.collection.immutable.Seq
import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

case class EventOutputTransformer(newEventNameInput: String,
                                  ingredientRenamesInput: java.util.Map[String, String]) extends common.EventOutputTransformer {
  override val newEventName: String = newEventNameInput
  override val ingredientRenames: Map[String, String] = ingredientRenamesInput.asScala.toMap
}