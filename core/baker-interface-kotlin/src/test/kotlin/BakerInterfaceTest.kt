import com.ing.baker.runtime.common.Baker
import org.junit.Assert.assertEquals
import org.junit.Test
import kotlin.math.pow
import kotlin.reflect.full.declaredFunctions

class BakerInterfaceTest {

    @Test
    fun `compare scala and kotlin interfaces`() {
        val bakerInterfaceNames = Baker::class.java.declaredMethods
            .filterNot { it.isSynthetic }
            .map { it.name.replace("\$default\$2", "") } // TODO improve this, the 2 should not be hardcoded
            .sorted()
            .drop(1) // Drop $init$

        val kotlinFunctionNames = mutableListOf<String>()

        com.ing.baker.runtime.kotlindsl.Baker::class
            .declaredFunctions
            .forEach { function ->
                val optionalParams = function.parameters.count { param -> param.isOptional }
                if (optionalParams == 0) {
                    kotlinFunctionNames.add(function.name)
                } else {
                    repeat(2.toDouble().pow(optionalParams.toDouble()).toInt()) {
                        kotlinFunctionNames.add(function.name)
                    }
                }
            }

        kotlinFunctionNames.add("fireEventAndResolveWhenReceived")
        kotlinFunctionNames.add("fireEventAndResolveWhenCompleted")
        kotlinFunctionNames.add("fireEventAndResolveOnEvent")
        kotlinFunctionNames.add("fireEvent")

        assertEquals(bakerInterfaceNames, kotlinFunctionNames.sorted())
    }
}
