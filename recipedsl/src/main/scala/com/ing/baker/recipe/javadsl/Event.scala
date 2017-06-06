//package com.ing.baker.newrecipe.javadsl
//
//import com.ing.baker.recipe.common
//
//
////TODO redo the event that its not trait but accepts a Class to create an event from
//trait Event
//  extends common.Event {
//  override val name: String = this.getClass.getSimpleName
//  override val providedIngredients: Seq[common.Ingredient] = this.getClass.getDeclaredFields.map(f => Ingredient(f.getName, f.getType))
//}
//
//case class EventImpl() extends Event