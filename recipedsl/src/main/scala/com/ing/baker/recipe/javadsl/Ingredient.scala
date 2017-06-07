package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common


case class Ingredient(override val name: String,
                      override val clazz: Class[_])extends common.Ingredient
