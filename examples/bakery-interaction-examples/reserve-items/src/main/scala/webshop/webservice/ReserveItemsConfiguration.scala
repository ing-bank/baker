package webshop.webservice

import org.springframework.context.annotation.{Bean, Configuration}

@Configuration
class ReserveItemsConfiguration {

  @Bean
  def ReserveItemsInstance(): ReserveItemsInstance = {
    new ReserveItemsInstance
  }
}
