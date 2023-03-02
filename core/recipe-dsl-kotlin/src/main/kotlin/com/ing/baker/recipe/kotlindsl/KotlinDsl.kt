package com.ing.baker.recipe.kotlindsl

import com.example.demo.ScalaExtensions.toScalaMap
import com.example.demo.ScalaExtensions.toScalaSeq
import com.example.demo.ScalaExtensions.toScalaSet
import com.ing.baker.recipe.common.EventOutputTransformer
import com.ing.baker.recipe.common.Ingredient
import com.ing.baker.recipe.javadsl.Event
import com.ing.baker.recipe.javadsl.InteractionDescriptor
import com.ing.baker.recipe.javadsl.Recipe
import com.ing.baker.types.Converters
import com.ing.baker.types.Value
import scala.Option
import kotlin.jvm.internal.CallableReference
import kotlin.reflect.KClass
import kotlin.reflect.KFunction
import kotlin.reflect.jvm.javaType

fun interactionFunctionToCommonInteraction(builder: InteractionBuilder): InteractionDescriptor {
   val inputIngredients = builder.func.parameters.drop(1)
      .map {
         val type = Converters.readJavaType(it.type.javaType)
         Ingredient(it.name, type)
      }

   return InteractionDescriptor(
      builder.func.ownerClass().simpleName,
      inputIngredients.toScalaSeq(),
      builder.events.map { Event(it.java, Option.empty()) }.toScalaSeq(),
      builder.requiredEvents.map { it.java.simpleName }.toScalaSet(),
      setOf<scala.collection.immutable.Set<String>>().toScalaSet(),
      mapOf<String, Value>().toScalaMap(),
      mapOf<String, String>().toScalaMap(),
      Option.empty(),
      Option.empty(),
      Option.empty(),
      mapOf<com.ing.baker.recipe.common.Event, EventOutputTransformer>().toScalaMap(),
      Option.empty(),
   )
}

fun convertRecipe(builder: RecipeBuilder): Recipe {
   return Recipe(builder.name)
      .withInteractions(builder.interactions.map(::interactionFunctionToCommonInteraction).toScalaSeq())
      .withSensoryEvents(builder.sensoryEvents.map { it.java }.toScalaSeq())

}

fun KFunction<*>.ownerClass(): KClass<*> {
   val owner = (this as CallableReference).owner
   return (owner as KClass<*>)
}



class InteractionsBuilder {

   var interactions: Set<InteractionBuilder> = setOf()

   fun interaction(func: KFunction<*>) {
      val builder = InteractionBuilder()
      builder.func(func)
      interactions =  interactions + builder
   }
   fun interaction(func: KFunction<*>, init: InteractionBuilder.() -> Unit) {
      val builder = InteractionBuilder()
      builder.apply(init)
      builder.func(func)
      interactions =  interactions + builder
   }

   fun build() = interactions
}

class InteractionBuilder {

   lateinit var func: KFunction<*>
   var events: Set<KClass<*>> = setOf()
   var requiredEvents: Set<KClass<*>> = setOf()

   fun func(func: KFunction<*>) {
      val sealedSubclasses = (func.returnType.classifier as KClass<*>).sealedSubclasses
      if (sealedSubclasses.isNotEmpty()) {
         this.events = sealedSubclasses.toSet()
      } else {
         this.events = setOf(func.returnType.classifier as KClass<*>)
      }

      this.func = func
   }

   fun events(vararg events: KClass<*>) {
      this.events = events.toSet()
   }

   fun requiredEvents(vararg requiredEvents: KClass<*>) {
      this.requiredEvents = requiredEvents.toSet()
   }
}


fun recipe(name: String, init: RecipeBuilder.() -> Unit): RecipeBuilder {
   val builder = RecipeBuilder()
   builder.name = name
   builder.apply(init)
   return builder
}

class RecipeBuilder {

   lateinit var name: String
   lateinit var interactions: Set<InteractionBuilder>
   lateinit var sensoryEvents: Set<KClass<*>>

   fun interactions(init: InteractionsBuilder.() -> Unit) {
      val builder = InteractionsBuilder()
      builder.apply(init)
      this.interactions = builder.build()
   }

   fun sensoryEvents(vararg sensoryEvents: KClass<*>) {
      this.sensoryEvents = sensoryEvents.toSet()
   }

}
