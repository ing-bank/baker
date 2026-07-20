package com.ing.baker.compiler

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.il.CompiledRecipe.NON_CRITICAL_VALIDATION_MESSAGE_PREFIX
import com.ing.baker.il.ValidationSettings
import com.ing.baker.recipe.common.Recipe
import org.slf4j.LoggerFactory
import scala.jdk.javaapi.CollectionConverters


object RecipeCompiler {

    private val logger = LoggerFactory.getLogger(RecipeCompiler::class.java)

    /**
     * Compile the given recipe to a technical recipe that is useful for Baker.
     *
     * @param recipe             ; The Recipe to compile and execute
     * @param validationSettings The validation settings to follow for the validation
     * @return
     */
    @JvmStatic
    fun compileRecipe(
        recipe: Recipe,
        validationSettings: ValidationSettings
    ): CompiledRecipe {
        // By default, Scala compiler has a precedence.
        // We want to migrate to Kotlin implementation and here we compare the results of both compilers to ensure they produce the same output.
        // In case of output difference, we add an error so that we can investigate and fix it before we can remove the Scala implementation.
        // Difference in recipe ID is expected and ignored, as it is generated differently in both implementations.
        val scala = RecipeCompilerScala.compileRecipe(recipe, validationSettings)
        val kotlin = RecipeCompilerKotlin.compileRecipe(recipe, validationSettings)

        val comparison = compareCompiledRecipes(scala, kotlin)

        if (comparison.isEquivalent)
            return scala

        // Add comparison failure to validation errors
        val updatedErrors = CollectionConverters.asJava(scala.validationErrors())
            .toMutableList()
            .apply { add("${NON_CRITICAL_VALIDATION_MESSAGE_PREFIX()} [COMPILATION FAILURE]: $comparison") }

        return CompiledRecipe(
            scala.name(),
            scala.recipeId(),
            scala.petriNet(),
            scala.initialMarking(),
            CollectionConverters.asScala(updatedErrors).toSeq(),
            scala.eventReceivePeriod(),
            scala.retentionPeriod()
        )
    }

    @JvmStatic
    fun compileRecipe(recipe: Recipe): CompiledRecipe =
        compileRecipe(recipe, ValidationSettings.defaultValidationSettings())

    /**
     * Compare two CompiledRecipe instances, ignoring the recipeId field.
     * Returns a ComparisonResult with details about any differences found.
     */
    private fun compareCompiledRecipes(scala: CompiledRecipe, kotlin: CompiledRecipe): ComparisonResult {
        val differences = mutableListOf<String>()

        // Compare name
        if (scala.name() != kotlin.name()) {
            differences.add("name: '${scala.name()}' vs '${kotlin.name()}'")
        }

        // Compare validation errors
        val scalaErrors = CollectionConverters.asJava(scala.validationErrors()).toSet()
        val kotlinErrors = CollectionConverters.asJava(kotlin.validationErrors()).toSet()
        if (scalaErrors != kotlinErrors) {
            differences.add("validationErrors: [${scalaErrors.joinToString(". ")}] vs [${kotlinErrors.joinToString(". ")}]")
        }

        // Compare event receive period
        if (scala.eventReceivePeriod() != kotlin.eventReceivePeriod()) {
            differences.add("eventReceivePeriod: ${scala.eventReceivePeriod()} vs ${kotlin.eventReceivePeriod()}")
        }

        // Compare retention period
        if (scala.retentionPeriod() != kotlin.retentionPeriod()) {
            differences.add("retentionPeriod: ${scala.retentionPeriod()} vs ${kotlin.retentionPeriod()}")
        }

        // Compare petri net structure
        val petriNetComparison = comparePetriNets(scala, kotlin)
        differences.addAll(petriNetComparison)

        // Compare initial marking
        val markingComparison = compareInitialMarking(scala, kotlin)
        differences.addAll(markingComparison)

        return ComparisonResult(differences.isEmpty(), differences)
            .also { comparison ->
                if (!comparison.isEquivalent) {
                    logger.error("Scala and Kotlin compilers produced different results: ${comparison.differences}")
                } else {
                    logger.debug("Scala and Kotlin compilers produced equivalent results")
                }
            }
    }

    private fun comparePetriNets(scala: CompiledRecipe, kotlin: CompiledRecipe): List<String> {
        val differences = mutableListOf<String>()
        val scalaNet = scala.petriNet()
        val kotlinNet = kotlin.petriNet()

        // Compare places - convert Scala collections to Java/Kotlin
        val scalaPlaces = CollectionConverters.asJava(scalaNet.places()).toSet()
        val kotlinPlaces = CollectionConverters.asJava(kotlinNet.places()).toSet()
        if (scalaPlaces != kotlinPlaces) {
            val scalaOnly = scalaPlaces - kotlinPlaces
            val kotlinOnly = kotlinPlaces - scalaPlaces
            if (scalaOnly.isNotEmpty()) {
                differences.add("places only in Scala: ${scalaOnly.joinToString { it.label() }}")
            }
            if (kotlinOnly.isNotEmpty()) {
                differences.add("places only in Kotlin: ${kotlinOnly.joinToString { it.label() }}")
            }
        }

        // Compare transitions
        val scalaTransitions = CollectionConverters.asJava(scalaNet.transitions()).toSet()
        val kotlinTransitions = CollectionConverters.asJava(kotlinNet.transitions()).toSet()
        if (scalaTransitions != kotlinTransitions) {
            val scalaOnly = scalaTransitions - kotlinTransitions
            val kotlinOnly = kotlinTransitions - scalaTransitions
            if (scalaOnly.isNotEmpty()) {
                differences.add("transitions only in Scala: ${scalaOnly.joinToString { it.label() }}")
            }
            if (kotlinOnly.isNotEmpty()) {
                differences.add("transitions only in Kotlin: ${kotlinOnly.joinToString { it.label() }}")
            }
        }

        // Compare sensory events - use Java accessor
        val scalaSensoryEvents = scala.sensoryEvents()
        val kotlinSensoryEvents = kotlin.sensoryEvents()
        if (scalaSensoryEvents != kotlinSensoryEvents) {
            val scalaSet = CollectionConverters.asJava(scalaSensoryEvents)
            val kotlinSet = CollectionConverters.asJava(kotlinSensoryEvents)
            differences.add("sensoryEvents differ: ${scalaSet.size} vs ${kotlinSet.size}")
        }

        // Compare all events - use Java accessor getAllEvents
        val scalaAllEvents = scala.getAllEvents()
        val kotlinAllEvents = kotlin.getAllEvents()
        if (scalaAllEvents != kotlinAllEvents) {
            val scalaSize = scalaAllEvents.size
            val kotlinSize = kotlinAllEvents.size
            differences.add("allEvents differ: $scalaSize vs $kotlinSize")
        }

        // Compare all ingredients - use Java accessor getAllIngredients
        val scalaAllIngredients = scala.getAllIngredients()
        val kotlinAllIngredients = kotlin.getAllIngredients()
        if (scalaAllIngredients != kotlinAllIngredients) {
            val scalaSize = scalaAllIngredients.size
            val kotlinSize = kotlinAllIngredients.size
            differences.add("allIngredients differ: $scalaSize vs $kotlinSize")
        }

        // Compare interaction transitions
        val scalaInteractionTransitions = CollectionConverters.asJava(scala.interactionTransitions()).toSet()
        val kotlinInteractionTransitions = CollectionConverters.asJava(kotlin.interactionTransitions()).toSet()
        if (scalaInteractionTransitions != kotlinInteractionTransitions) {
            differences.add("interactionTransitions differ: ${scalaInteractionTransitions.size} vs ${kotlinInteractionTransitions.size}")
        }

        return differences
    }

    private fun compareInitialMarking(scala: CompiledRecipe, kotlin: CompiledRecipe): List<String> {
        val differences = mutableListOf<String>()
        val scalaMarking = scala.initialMarking()
        val kotlinMarking = kotlin.initialMarking()

        if (scalaMarking != kotlinMarking) {
            differences.add("initialMarking differs")
            // More detailed comparison if needed
            val scalaMarkingJava = CollectionConverters.asJava(scalaMarking)
            val kotlinMarkingJava = CollectionConverters.asJava(kotlinMarking)
            if (scalaMarkingJava.size != kotlinMarkingJava.size) {
                differences.add("initialMarking size: ${scalaMarkingJava.size} vs ${kotlinMarkingJava.size}")
            }
        }

        return differences
    }

    /**
     * Result of comparing two CompiledRecipe instances.
     */
    data class ComparisonResult(
        val isEquivalent: Boolean,
        val differences: List<String>
    ) {
        override fun toString(): String {
            return if (isEquivalent) {
                "CompiledRecipes are equivalent (ignoring recipeId)"
            } else {
                "CompiledRecipes differ:\n${differences.joinToString("\n  - ", "  - ")}"
            }
        }
    }
}
