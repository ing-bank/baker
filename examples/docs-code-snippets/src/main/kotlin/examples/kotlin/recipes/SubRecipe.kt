package examples.kotlin.recipes

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe

@ExperimentalDsl
object SubRecipe {

    val myRecipe = recipe("root recipe") {
        subRecipe(recipe("sub recipe 1"))
        subRecipe(recipe("sub recipe 2") {
            recipe("sub sub recipe 2.1")
        })
    }

}