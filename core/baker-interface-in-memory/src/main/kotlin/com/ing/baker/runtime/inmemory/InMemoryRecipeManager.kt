package com.ing.baker.runtime.inmemory

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.common.RecipeRecord
import com.ing.baker.runtime.model.RecipeManager
import com.typesafe.scalalogging.Logger
import org.slf4j.LoggerFactory
import scala.Option
import scala.jdk.CollectionConverters.MapHasAsScala
import java.util.concurrent.ConcurrentHashMap
import scala.collection.Map as ScalaMap

class InMemoryRecipeManager : RecipeManager<InMemoryEffect<*>> {

    private val store = ConcurrentHashMap<String, RecipeRecord>()

    override fun logger(): Logger = Logger(LoggerFactory.getLogger(javaClass.name))

    @Suppress("UNCHECKED_CAST")
    override fun store(compiledRecipe: CompiledRecipe, timestamp: Long): InMemoryEffect<Any> =
        store.put(
            compiledRecipe.recipeId(),
            RecipeRecord.of(compiledRecipe, timestamp, true, true)
        ).let { InMemoryEffects.unit() as InMemoryEffect<Any> }

    override fun fetch(recipeId: String): InMemoryEffect<Option<RecipeRecord>> =
        InMemoryEffects.pure(Option.apply(store[recipeId]))

    override fun fetchAll(): InMemoryEffect<ScalaMap<String, RecipeRecord>> =
        InMemoryEffects.pure(
            ScalaMap.from(MapHasAsScala(store).asScala()) as ScalaMap<String, RecipeRecord>
        )
}
