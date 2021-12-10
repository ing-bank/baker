package com.ing.bakery.baker.spring;

import com.ing.bakery.baker.Bakery;
import com.ing.bakery.baker.BakeryExecutorJava;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.ApplicationContext;
import org.springframework.context.annotation.Bean;
import scala.Some;

public class BakeryExecutorConfiguration {

  @Autowired private ApplicationContext applicationContext;

  @Bean BakeryExecutorJava bakeryExecutor() {
    return new BakeryExecutorJava(Bakery.instance(new Some(applicationContext)));
  }

}
