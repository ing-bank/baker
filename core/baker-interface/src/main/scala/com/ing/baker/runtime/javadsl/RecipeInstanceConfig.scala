package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.model.recipeinstance.RecipeInstance

import java.time.Duration
import java.util.Optional
import scala.concurrent.duration.{FiniteDuration, NANOSECONDS}
import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.jdk.OptionConverters.RichOptional

case class RecipeInstanceConfig(idleTTL: Optional[Duration] = Optional.of(Duration.ofSeconds(5)),
                                ingredientsFilter: java.util.List[String] = java.util.List.of()) {

  def withIdleTTL(idleTTL: Optional[Duration]) = copy(idleTTL = idleTTL)

  def withIngredientsFilter(ingredientsFilter: java.util.List[String]) = ingredientsFilter

  def toBakerFRecipeInstanceConfig(): RecipeInstance.Config = {
    RecipeInstance.Config(
      idleTTL.toScala.map(duration => FiniteDuration.apply(duration.toNanos, NANOSECONDS)),
      ingredientsFilter.asScala.toSeq
    )
  }
}
