package com.ing.baker.il

import scala.collection.immutable.Seq
/**
  * Describes an event.
  *
  * @param name The name of an event.
  * @param ingredients The ingredients the event produces.
  */
case class EventDescriptor(name: String,
                           ingredients: Seq[IngredientDescriptor]) {

  // Used in CompiledRecipe to generate the hash. This is a workaround to keep the hash the same.
  // This method mimics the result of toString before ingredients was of type scala.collection.immutable.Seq[IngredientDescriptor].
  override def toString : String = {
    val ingredientsString = {
      if (ingredients.isInstanceOf[List[IngredientDescriptor]])
        ingredients.mkString(start = "List(", sep = ", ", end = ")")
      else if (ingredients.isEmpty) "ArrayBuffer()"
      else ingredients.mkString(start = "ArraySeq(", sep = ", ", end = ")")
    }

    s"EventDescriptor($name,$ingredientsString)"
  }

}