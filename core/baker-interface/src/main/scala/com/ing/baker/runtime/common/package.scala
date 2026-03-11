package com.ing.baker.runtime

package object common {

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
  private[runtime] def unmock(clazz: Class[_]) = {
    if (clazz.getName.startsWith("org.mockito.codegen.")) {
      // Handle mockito-inline's ByteBuddy generated classes FIRST
      // These mocks implement the original interface/class, so we need to find it from interfaces or superclass
      val interfaces = clazz.getInterfaces
      if (interfaces.nonEmpty && !interfaces.head.getName.startsWith("org.mockito")) {
        // Return the first non-Mockito interface
        interfaces.head
      } else {
        // Try the superclass
        val superclass = clazz.getSuperclass
        if (superclass != null && superclass != classOf[Object] && !superclass.getName.startsWith("org.mockito")) {
          superclass
        } else {
          // Last resort: return the class as-is if we can't find the original
          clazz
        }
      }
    } else if (clazz.getName.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = clazz.getName.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      clazz.getClassLoader.loadClass(originalName)
    } else if (clazz.getName.contains("$MockitoMock$")) {
      val originalName: String = clazz.getName.split("\\$MockitoMock\\$")(0)
      clazz.getClassLoader.loadClass(originalName)
    } else
      clazz
  }
}
