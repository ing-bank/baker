package com.ing.baker.runtime.scaladsl

import java.util.Optional

import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.types.Type

import scala.collection.immutable.Seq
import scala.collection.JavaConverters._

case class InteractionInstanceDescriptor(id : String,
                                         name: String,
                                         input: Seq[InteractionInstanceInput],
                                         output: Option[Map[String, Map[String, Type]]] = None)
  extends common.InteractionInstanceDescriptor with ScalaApi { self =>

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override type Input = InteractionInstanceInput

  def asJava(): javadsl.InteractionInstanceDescriptor =
    javadsl.InteractionInstanceDescriptor(id, name, input.map(_.asJava).asJava, Optional.ofNullable(output.map(_.map(e => (e._1, e._2.asJava)).asJava).orNull))

}
