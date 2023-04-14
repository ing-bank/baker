import com.ing.baker.runtime.common.Baker
import org.junit.Assert.assertEquals
import org.junit.Test
import java.lang.reflect.Method
import kotlin.math.pow
import kotlin.reflect.full.declaredFunctions

class BakerInterfaceTest {

    @Test
    fun `compare Scala and Kotlin Baker interfaces`() {
        assertEquals(methodsInScalaInterface(), methodsInKotlinInterface())
    }

    private fun methodsInScalaInterface() = Baker::class.java.declaredMethods
        .filterNot { it.isSynthetic }
        .map { it.sanitizedName() }
        .filterNot { it == "\$init\$" }
        .sorted()

    // Scala functions with default arguments have $default$ in their name.
    private fun Method.sanitizedName() = if (name.contains("\$default\$")) {
        name.split("\$default\$").first()
    } else {
        name
    }

    private fun methodsInKotlinInterface(): List<String> {
        val methodNames = mutableListOf<String>()

        com.ing.baker.runtime.kotlindsl.Baker::class
            .declaredFunctions
            .forEach { function ->
                val defaultArgumentsCount = function.parameters.count { param -> param.isOptional }
                if (defaultArgumentsCount != 0) {
                    // The Kotlin interface uses default arguments instead of overloads. As a result the Kotlin
                    // interface has fewer methods. We correct that here.
                    repeat(2.toDouble().pow(defaultArgumentsCount.toDouble()).toInt()) {
                        methodNames.add(function.name)
                    }
                } else {
                    methodNames.add(function.name)
                }
            }

        // We removed a couple of nonsensical overloads from the Kotlin interface. We need to add them here so the
        // comparison does not fail.
        methodNames.add("fireEventAndResolveWhenReceived")
        methodNames.add("fireEventAndResolveWhenCompleted")
        methodNames.add("fireEventAndResolveOnEvent")
        methodNames.add("fireEvent")

        return methodNames.sorted()
    }
}
