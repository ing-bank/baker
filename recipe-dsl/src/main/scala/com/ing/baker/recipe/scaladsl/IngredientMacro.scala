package com.ing.baker.recipe.scaladsl

import scala.reflect.runtime.universe.TypeTag

import scala.language.experimental.macros
import scala.reflect.NameTransformer.LOCAL_SUFFIX_STRING
import scala.reflect.macros.blackbox

object ngredient {
  def apply[T: TypeTag]: Ingredient[T] = macro ingredientImpl[T]

  /** Detect the enclosing name of an expression.
    * For example: `val x = "name is " + getName` will set `x` to the string `"name is x"`.
    *
    * @return String that represents the name of the enclosing value.
    */
  def getEnclosingName(c: blackbox.Context): String = {
    c.internal.enclosingOwner
      .name.decodedName.toString
      .stripSuffix(LOCAL_SUFFIX_STRING).stripSuffix("$lzy")
  }

  def ingredientImpl[T: c.WeakTypeTag](c: blackbox.Context)(typeTagT: c.Tree): c.Tree = {

    import c.universe._


    val ingredientName = getEnclosingName(c)
    val ingredientValueType = c.weakTypeOf[T]
    q"Ingredient[$ingredientValueType]($ingredientName)($typeTagT)"
  }
}
