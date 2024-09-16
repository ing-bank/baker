import com.ing.baker.runtime.kotlindsl.functionInteractionInstance
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
        val func = { test: String -> "" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
    }

    @Test
    fun `should handle function interaction list`() {
        val func = { test: String -> listOf("") }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
    }
}
