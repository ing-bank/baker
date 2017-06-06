//package com.ing.baker.newrecipe.javadsl
//
//import java.lang.reflect.Method
//
//import com.ing.baker.newrecipe.common
//import com.ing.baker.newrecipe.common._
//import com.ing.baker.recipe.annotations
//
//trait Interaction extends common.Interaction {
//
//  override val name: String = this.getClass.getSimpleName
//  //TODO create a seq of input ingredients from the @RequiredIngredient tag
//  override val inputIngredients: Seq[Ingredient] = Seq.empty
//
//  private val interactionMethodName: String = "apply"
//  private val method: Method = this.getClass.getDeclaredMethods
//    .find(_.getName == interactionMethodName)
//    .getOrElse(throw new IllegalStateException(
//      s"No method named '$interactionMethodName' defined on '${this.getClass.getName}'"))
//
//  override val output: InteractionOutput = {
//    //ProvidesIngredient
//    if(method.isAnnotationPresent(classOf[annotations.ProvidesIngredient]))
//    {
//      val interactionOutputName: String = method.getAnnotation(classOf[annotations.ProvidesIngredient]).value()
//      ProvidesIngredient(Ingredient(interactionOutputName, method.getReturnType))
//    }
//    //ProvidesEvent
//    else if(method.isAnnotationPresent(classOf[annotations.FiresEvent])) {
//      val outputEventClasses: Seq[Class[_]] = method.getAnnotation(classOf[annotations.FiresEvent]).oneOf().toSeq
//      //Create events from classes and create ingredients for each field
//      val events: Seq[Event] = outputEventClasses.map(
//        _ match {
//          case event: Class[_ <: Event] => Event()
//          case _ => throw new RecipeException()
//        })
//      FiresOneOfEvents(events)
//    }
//    //ProvidesNothing
//    else ProvidesNothing
//  }
//}
