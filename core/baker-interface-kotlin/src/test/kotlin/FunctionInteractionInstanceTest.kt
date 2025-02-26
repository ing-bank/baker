import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.kotlindsl.functionInteractionInstance
import com.ing.baker.types.Converters
import com.ing.baker.types.Value
import org.junit.Assert.assertEquals
import org.junit.Test
import java.util.*

class FunctionInteractionInstanceTest {
    @Test
    fun `should handle function interaction with optional`() {
        val func = @JvmSerializableLambda { test: Optional<String> -> "Empty: ${test.isEmpty}" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals("\$SieveInteraction\$test", interaction.name())
        assertEquals("Empty: false", callInteraction<String>(mapOf("test" to Optional.of("test")), interaction))

    }

    @Test
    fun `should handle function interaction with empty optional`() {
        val func = @JvmSerializableLambda { test: Optional<String> -> "Empty: ${test.isEmpty}" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals("\$SieveInteraction\$test", interaction.name())
        assertEquals("Empty: true", callInteraction<String>(mapOf("test" to Optional.empty<String>()), interaction))

    }

    @Test
    fun `should handle function interaction`() {
        val func = @JvmSerializableLambda { test: String -> "Output: $test" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals("\$SieveInteraction\$test", interaction.name())
        assertEquals("Output: value", callInteraction<String>(mapOf("test" to "value"), interaction))
    }

    @Test
    fun `should handle function interaction with multiple ingredients`() {
        val func = @JvmSerializableLambda { test1: String, test2: Int, test3: Boolean -> "$test1: ${if (test3) 2*test2 else test2}" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals("\$SieveInteraction\$test", interaction.name())
        assertEquals("calculation: 10", callInteraction<String>(mapOf("test1" to "calculation", "test2" to 5, "test3" to true), interaction))
    }


    @Test
    fun `should handle function interaction list`() {
        val func = @JvmSerializableLambda { test: String -> listOf(test, test) }
        val interaction = functionInteractionInstance("test", func)

        assertEquals("\$SieveInteraction\$test", interaction.name(), )
        assertEquals(listOf("input", "input"), callInteractionList<String>(mapOf("test" to "input"), interaction))

    }

    private val emptyMetaMap = scala.collection.immutable.Map.from(
        scala.jdk.CollectionConverters.MapHasAsScala(
            emptyMap<String, String>()
        ).asScala())

    private inline fun <reified T: Any> callInteraction(ingredients: Map<String, Any>, interaction: InteractionInstance): T? {
        return executeInteraction(interaction, ingredients).`as`(T::class.java)
    }

    private inline fun <reified T: Any> callInteractionList(ingredients: Map<String, Any>, interaction: InteractionInstance): List<T>? {
        return executeInteraction(interaction, ingredients).asList(T::class.java)
    }

    private fun executeInteraction(interaction: InteractionInstance, ingredients: Map<String, Any>): Value =
        interaction.execute(
            ingredients.map { IngredientInstance(it.key, Converters.toValue(it.value)) }, emptyMetaMap
    ).get().get().providedIngredients.values.first()

}
