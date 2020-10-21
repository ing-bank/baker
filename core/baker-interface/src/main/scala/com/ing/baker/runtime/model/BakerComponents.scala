package com.ing.baker.runtime.model

case class BakerComponents[F[_]](
                               interactionInstanceManager: InteractionInstanceManager[F],
                               recipeInstanceManager: RecipeInstanceManager[F],
                               recipeManager: RecipeManager[F],
                               eventStream: EventStream[F]
                             )
