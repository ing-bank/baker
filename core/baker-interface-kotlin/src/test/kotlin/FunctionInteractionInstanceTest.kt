import com.ing.baker.runtime.kotlindsl.functionInteractionInstance
import org.junit.Assert.assertEquals
import org.junit.Test

class FunctionInteractionInstanceTest {


    @Test
    fun `should handle function interaction`() {
        val func = { test: String -> "" }
        val interaction = functionInteractionInstance("test", func)

        assertEquals(interaction.name(), "\$SieveInteraction\$test")
    }
}
