package com.ing.baker.runtime.model

case class BakerComponents[F[_]](interactions: InteractionsF[F],
                                 recipeInstanceManager: RecipeInstanceManager[F],
                                 recipeManager: RecipeManager[F],
                                 eventStream: EventStream[F],
                                 logging: BakerLogging = BakerLogging())
