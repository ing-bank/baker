import org.junit.Assert.fail
import org.junit.Test
import java.lang.reflect.Method
import kotlin.math.pow
import kotlin.reflect.full.declaredFunctions

class KotlinBakerInterfaceTest {

    @Test
    fun `compare Scala and Kotlin Baker interfaces`() {
        @Suppress("ConvertArgumentToSet") // Some method names occur multiple times due to overloads
        val missingInKotlinInterface = methodsInScalaInterface().minus(methodsInKotlinInterface())

        if (missingInKotlinInterface.isNotEmpty()) {
            fail("Failed to find $missingInKotlinInterface in the Kotlin interface")
        }
    }

    private fun methodsInScalaInterface() = com.ing.baker.runtime.common.Baker::class.java.declaredMethods
        .filterNot { it.isSynthetic }
        .map { it.sanitizedName() }
        .filterNot { it == "\$init\$" }

    // Scala functions with default arguments have $default$ in their name.
    private fun Method.sanitizedName() = if (name.contains("\$default\$")) {
        name.split("\$default\$").first()
    } else {
        name
    }

    private fun methodsInKotlinInterface(): List<String> {
        val methodNames = com.ing.baker.runtime.kotlindsl.Baker::class.declaredFunctions
            .fold(initial = mutableListOf<String>()) { names, kFunction ->
                // The Kotlin interface uses default arguments instead of overloads. As a result the Kotlin
                // interface has fewer methods. We correct that here.
                val defaultArgumentsCount = kFunction.parameters.count { param -> param.isOptional }
                if (defaultArgumentsCount != 0) {
                    repeat(2.toDouble().pow(defaultArgumentsCount.toDouble()).toInt()) {
                        names.add(kFunction.name)
                    }
                } else {
                    names.add(kFunction.name)
                }
                names
            }

        // The Scala interface contains a couple of nonsensical overloads. These no longer exist in the Kotlin DSL.
        // We take these cases into account here so the comparison does not fail.
        return methodNames.apply {
            add("fireEventAndResolveWhenReceived")
            add("fireEventAndResolveWhenCompleted")
            add("fireEventAndResolveOnEvent")
            add("fireEvent")
        }
    }
}
