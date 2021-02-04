package com.ing.bakery.interaction.spring

import com.ing.baker.recipe.javadsl.Interaction
import org.springframework.context.annotation.{Bean, Configuration}

@Configuration
class TestConfiguration {
  @Bean
  def getImplementationOne: Interaction = {
    new TestInteraction("Interaction one")
  }

  @Bean
  def getImplementationOneAnotherCopy: Interaction = {
    new TestInteraction("Interaction one another copy")
  }
}