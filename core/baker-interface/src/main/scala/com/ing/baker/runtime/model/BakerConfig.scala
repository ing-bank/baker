package com.ing.baker.runtime.model

import com.ing.baker.runtime.model.recipeinstance.RecipeInstanceConfig

import java.time.Duration

object BakerConfig {
  def default(): BakerConfig = {
    new BakerConfig(
      false,
      RecipeInstanceConfig(),
      Duration.ofSeconds(60),
      Duration.ofSeconds(10),
      Duration.ofSeconds(10),
      Duration.ofSeconds(10),
      Duration.ofSeconds(60),
      Duration.ofSeconds(10),
      Duration.ofSeconds(10),
      Duration.ofSeconds(60)
    )
  }
}

case class BakerConfig(
                   allowAddingRecipeWithoutRequiringInstances: Boolean,
                   recipeInstanceConfig: RecipeInstanceConfig,
                   idleTimeout: Duration,
                   retentionPeriodCheckInterval: Duration,
                   bakeTimeout: Duration,
                   processEventTimeout: Duration,
                   inquireTimeout: Duration,
                   shutdownTimeout: Duration,
                   addRecipeTimeout: Duration,
                   executeSingleInteractionTimeout: Duration) {
  def withAllowAddingRecipeWithoutRequiringInstances(allowAddingRecipeWithoutRequiringInstances: Boolean): BakerConfig =
    copy(allowAddingRecipeWithoutRequiringInstances = allowAddingRecipeWithoutRequiringInstances)

  def withRecipeInstanceConfig(recipeInstanceConfig: RecipeInstanceConfig): BakerConfig =
    copy(recipeInstanceConfig = recipeInstanceConfig)

  def withIdleTimeout(idleTimeout: Duration): BakerConfig =
    copy(idleTimeout = idleTimeout)

  def withRetentionPeriodCheckInterval(retentionPeriodCheckInterval: Duration): BakerConfig =
    copy(retentionPeriodCheckInterval = retentionPeriodCheckInterval)

  def withBakeTimeout(bakeTimeout: Duration): BakerConfig =
    copy(bakeTimeout = bakeTimeout)

  def withProcessEventTimeout(processEventTimeout: Duration): BakerConfig =
    copy(processEventTimeout = processEventTimeout)

  def withInquireTimeout(inquireTimeout: Duration): BakerConfig =
    copy(inquireTimeout = inquireTimeout)

  def withShutdownTimeout(shutdownTimeout: Duration): BakerConfig =
    copy(shutdownTimeout = shutdownTimeout)

  def withAddRecipeTimeout(addRecipeTimeout: Duration): BakerConfig =
    copy(addRecipeTimeout = addRecipeTimeout)

  def withExecuteSingleInteractionTimeout(executeSingleInteractionTimeout: Duration): BakerConfig =
    copy(executeSingleInteractionTimeout = executeSingleInteractionTimeout)
}
