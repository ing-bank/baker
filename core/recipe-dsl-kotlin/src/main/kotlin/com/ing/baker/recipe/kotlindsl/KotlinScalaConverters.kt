package com.ing.baker.recipe.kotlindsl

import scala.Option
import scala.Some

fun Any?.toScalaOption(): Option<Any> = this?.let { Some(it) } ?: Option.empty()
