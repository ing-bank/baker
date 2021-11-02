package com.ing.baker.test

import org.scalatest.Suites
import org.scalatestplus.junit.JUnitWrapperSuite

class JavaJunitTests extends Suites(
  new JUnitWrapperSuite(classOf[com.ing.baker.test.javadsl.EventsFlowTest].getName, ClassLoader.getSystemClassLoader),
  new JUnitWrapperSuite(classOf[com.ing.baker.test.javadsl.RecipeAssertTest].getName, ClassLoader.getSystemClassLoader)
)
