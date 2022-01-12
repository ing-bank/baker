package com.ing.baker.runtime.akka.java

import java.util.{List => JavaList}

import akka.actor.ActorSystem
import com.ing.baker.runtime.akka.AkkaBakerConfig
import com.ing.baker.runtime.akka.internal.CachingInteractionManager
import com.ing.baker.runtime.javadsl
import com.ing.baker.runtime.recipe_manager.{DefaultRecipeManager, RecipeManager}
import com.typesafe.config.Config
import net.ceedubs.ficus.Ficus._

object AkkaBaker {
  def apply(config: Config, actorSystem: ActorSystem, interactions: CachingInteractionManager, recipeManager: RecipeManager): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem, interactions, recipeManager))

  def apply(config: Config, actorSystem: ActorSystem): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem, CachingInteractionManager(), DefaultRecipeManager.pollingAware(actorSystem.dispatcher)))

  def apply(config: Config, actorSystem: ActorSystem, interactions: JavaList[AnyRef]): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.apply(config, actorSystem,
      CachingInteractionManager.fromJava(interactions, config.getOrElse[Boolean]("baker.interactions.allow-superset-for-output-types", false))))

  def fromAkkaBakerConfig(config: AkkaBakerConfig): javadsl.Baker =
    new javadsl.Baker(com.ing.baker.runtime.akka.AkkaBaker.fromAkkaBakerConfig(config))

}
