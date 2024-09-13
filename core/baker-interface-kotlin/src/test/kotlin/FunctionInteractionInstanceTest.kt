import com.ing.baker.runtime.javadsl.IngredientInstance
import com.ing.baker.runtime.javadsl.InteractionInstance
import com.ing.baker.runtime.kotlindsl.functionInteractionInstance
import com.ing.baker.types.Converters
import org.junit.Assert.assertEquals
import org.junit.Test
import java.util.*

class FunctionInteractionInstanceTest {
    @Test
    fun `should handle function interaction with optional`() {
        val func = { test: Optional<String> -> "" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
    }

    @Test
    fun `should handle function interaction`() {
        val func = { test: String -> "Output: $test" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
        assertEquals(callInteraction<String>(mapOf("test" to "value"), interaction), "Output: value")
    }

    @Test
    fun `should handle function interaction with multiple ingredients`() {
        val func = { test1: String, test2: Int, test3: Boolean -> "$test1: ${if (test3) 2*test2 else test2}" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
        assertEquals(callInteraction<String>(mapOf("test1" to "calculation", "test2" to 5, "test3" to true), interaction), "calculation: 10")
    }


    @Test
    fun `should handle function interaction list`() {
        val func = { test: String -> listOf("") }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
    }

    private val emptyMetaMap = scala.collection.immutable.Map.from(
        scala.jdk.CollectionConverters.MapHasAsScala(
            emptyMap<String, String>()
        ).asScala())

    private inline fun <reified T: Any> callInteraction(ingredients: Map<String, Any>, interaction: InteractionInstance): T? =
        interaction.execute(
            ingredients.map { IngredientInstance(it.key, Converters.toValue(it.value)) }, emptyMetaMap
        ).get().get().providedIngredients.values.first().`as`(T::class.java)


}
