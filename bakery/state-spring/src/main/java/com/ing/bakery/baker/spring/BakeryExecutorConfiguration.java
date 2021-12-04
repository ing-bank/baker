package com.ing.bakery.baker.spring;

import com.ing.bakery.baker.Bakery;
import com.ing.bakery.baker.BakeryExecutorJava;
import org.springframework.context.annotation.Bean;

public class BakeryExecutorConfiguration {

  @Bean BakeryExecutorJava bakeryExecutor() {
    return new BakeryExecutorJava(Bakery.instance());
  }

}
