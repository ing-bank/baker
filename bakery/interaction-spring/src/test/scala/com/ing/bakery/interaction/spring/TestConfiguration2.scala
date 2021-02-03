package com.ing.bakery.interaction.spring

import com.ing.baker.recipe.javadsl.Interaction
import org.springframework.context.annotation.{Bean, Configuration}

@Configuration
class TestConfiguration2 {
  @Bean
  def getImplementationThree: Interaction = {
    new TestInteraction("Interaction three")
  }

  @Bean
  def getImplementationFour: Interaction = {
    new TestInteraction("Interaction four")
  }
}