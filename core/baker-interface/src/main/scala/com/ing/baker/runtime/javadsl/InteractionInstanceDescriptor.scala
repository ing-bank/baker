package com.ing.baker.runtime.javadsl

import java.util
import java.util.Optional

import com.ing.baker.runtime.{common, scaladsl}
import com.ing.baker.runtime.common.LanguageDataStructures.JavaApi
import com.ing.baker.types.Type

import scala.collection.JavaConverters._

case class InteractionInstanceDescriptor(id : String,
                                         name: String,
                                         input: util.List[InteractionInstanceInput],
                                         output: Optional[util.Map[String, util.Map[String, Type]]] = Optional.empty())
  extends common.InteractionInstanceDescriptor with JavaApi { self =>

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override type Input = InteractionInstanceInput

  def getId(): String = id

  def getName(): String = name

  def getInput(): util.List[InteractionInstanceInput] = input

  def getOutput(): Optional[util.Map[String, util.Map[String, Type]]] = output

  def asScala(): scaladsl.InteractionInstanceDescriptor =
    scaladsl.InteractionInstanceDescriptor(id, name, input.asScala.map(_.asScala).toIndexedSeq,
      Option.apply(output.orElse(null)).map(_.asScala.map(e => (e._1, e._2.asScala.toMap)).toMap)
    )
}
