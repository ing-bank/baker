package com.ing.baker.runtime.javadsl

import com.ing.baker.runtime.model.BakerF

import java.time.Duration
import scala.concurrent.duration.{FiniteDuration, NANOSECONDS}

object BakerConfig {
  def defaults(): BakerConfig = {
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
                   val allowAddingRecipeWithoutRequiringInstances: Boolean,
                   val recipeInstanceConfig: RecipeInstanceConfig,
                   val idleTimeout: Duration,
                   val retentionPeriodCheckInterval: Duration,
                   val bakeTimeout: Duration,
                   val processEventTimeout: Duration,
                   val inquireTimeout: Duration,
                   val shutdownTimeout: Duration,
                   val addRecipeTimeout: Duration,
                   val executeSingleInteractionTimeout: Duration) {
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

  def toBakerFConfig(): BakerF.Config = {
    implicit def toScalaDuration(duration: Duration): FiniteDuration = FiniteDuration.apply(duration.toNanos, NANOSECONDS)

    BakerF.Config(
      allowAddingRecipeWithoutRequiringInstances,
      recipeInstanceConfig.toBakerFRecipeInstanceConfig(),
      idleTimeout,
      retentionPeriodCheckInterval,
      bakeTimeout,
      processEventTimeout,
      inquireTimeout,
      shutdownTimeout,
      addRecipeTimeout,
      executeSingleInteractionTimeout
    )
  }
}
