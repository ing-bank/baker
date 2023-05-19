import org.junit.Assert.fail
import org.junit.Test
import java.lang.reflect.Method
import kotlin.math.pow
import kotlin.reflect.full.declaredFunctions

class BakerInterfaceTest {

    @Test
    fun `compare methods in Scala trait and Kotlin Baker class`() {
        @Suppress("ConvertArgumentToSet") // Some method names occur multiple times due to overloads
        val missingInKotlinInterface = methodsInScalaTrait().minus(methodsInKotlinClass())

        if (missingInKotlinInterface.isNotEmpty()) {
            fail("Failed to find $missingInKotlinInterface in the Kotlin interface")
        }
    }

    private fun methodsInScalaTrait() = com.ing.baker.runtime.common.Baker::class.java.declaredMethods
        .filterNot { it.isSynthetic }
        .map { it.sanitizedName() }
        .filterNot { it == "\$init\$" }

    // Scala methods with default arguments have $default$ in their name.
    private fun Method.sanitizedName() = if (name.contains("\$default\$")) {
        name.split("\$default\$").first()
    } else {
        name
    }

    private fun methodsInKotlinClass(): List<String> {
        val methodNames = com.ing.baker.runtime.kotlindsl.Baker::class.declaredFunctions
            .fold(initial = emptyList<String>()) { names, kFunction ->
                // The Kotlin implementation uses default arguments instead of overloads. As a result the Kotlin
                // interface has fewer methods. We correct that here.
                val defaultArgumentsCount = kFunction.parameters.count { param -> param.isOptional }
                if (defaultArgumentsCount != 0) {
                    names + List(2.toDouble().pow(defaultArgumentsCount.toDouble()).toInt()) { kFunction.name }
                } else {
                    names + kFunction.name
                }
            }

        // The Scala interface contains a couple of nonsensical overloads. These no longer exist in the Kotlin DSL.
        // We take these cases into account here so the comparison does not fail.
        return methodNames + listOf(
            "fireEventAndResolveWhenReceived",
            "fireEventAndResolveWhenCompleted",
            "fireEventAndResolveOnEvent",
            "fireEvent"
        )
    }
}
