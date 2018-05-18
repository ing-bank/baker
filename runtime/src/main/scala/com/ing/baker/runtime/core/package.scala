package com.ing.baker.runtime

package object core {

  /**
    * Mockito breaks reflection when mocking classes, for example:
    *
    * interface A { }
    * class B extends A
    * val b = mock[B]
    *
    * When inspecting b, the fact that it extends from A can no longer be reflected.
    *
    * Here we obtain the original class that was mocked.
    *
    * @param clazz The (potentially mocked) class
    * @return The original class
    */
  def unmock(clazz: Class[_]) = {

    if (clazz.getName.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = clazz.getName.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      clazz.getClassLoader.loadClass(originalName)
    } else
      clazz
  }

}
