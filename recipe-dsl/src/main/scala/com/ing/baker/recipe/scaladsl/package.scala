package com.ing.baker.recipe

package object scaladsl {
  implicit def InteractionToInteractionDescriptor(interaction: Interaction): InteractionDescriptor = InteractionDescriptorFactory(interaction)

  implicit def InteractionToInteractionDescriptorWithRename(interactionNameTuple:(Interaction, String)): InteractionDescriptor = InteractionDescriptorFactory(interactionNameTuple._1, interactionNameTuple._2)


  implicit def IngredientToIngredientSeq(ingredient: common.Ingredient): Seq[common.Ingredient] = Seq(ingredient)

  implicit def StringToRecipe(name: String): Recipe = Recipe(name)

  val processId: Ingredient[_] = new Ingredient[String](common.ProcessIdName)

  object Ingredients {
    def apply(ingredients: common.Ingredient*): Seq[common.Ingredient] = ingredients.toSeq
  }

  implicit class InteractionOps(i: Interaction) {

    // TODO use shapeless to abstract over function arity and add type safety
    def implement[A](fn: A => Map[String, Any]): (String, Seq[Any] => Any) =
      i.name -> (input => fn(input(0).asInstanceOf[A]))

    def implement[A, B](fn: (A, B) => Map[String, Any]): (String, Seq[Any] => Any) =
      i.name -> (input => fn(input(0).asInstanceOf[A], input(1).asInstanceOf[B]))

    def implement[A, B, C](fn: (A, B, C) => Map[String, Any]): (String, Seq[Any] => Any) =
      i.name -> (input => fn(input(0).asInstanceOf[A], input(1).asInstanceOf[B], input(2).asInstanceOf[C]))
  }

  implicit class EventOps(e: Event) {
    def instance(values: Any*): Map[String, Any] = {
      // TODO the event name is stringy typed since DSL and Runtime don't know each other, should be fixed
      e.providedIngredients.map(_.name).zip(values.toSeq).toMap + ("$EventName$" -> e.name)
    }
  }

  implicit class IngredientMapOps(ingredients: Map[String, Any]) {

    def get[T](ingredient: Ingredient[T]): Option[T] = ingredients.get(ingredient.name).map(_.asInstanceOf[T])
  }

}


