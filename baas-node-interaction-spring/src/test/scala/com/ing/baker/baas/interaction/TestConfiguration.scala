package com.ing.baker.baas.interaction

import com.ing.baker.recipe.javadsl.Interaction
import org.springframework.context.annotation.{Bean, Configuration}

@Configuration
class TestConfiguration {
  @Bean
  def getImplementationOne: Interaction = {
    new TestInteraction("Interaction one")
  }

  @Bean
  def getImplementationTwo: Interaction = {
    new TestInteraction("Interaction two")
  }
}