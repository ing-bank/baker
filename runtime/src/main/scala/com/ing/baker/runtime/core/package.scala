package com.ing.baker.runtime

package object core {

  def unmock(clazz: Class[_]) = {

    if (clazz.getName.contains("$$EnhancerByMockitoWithCGLIB$$")) {
      val originalName: String = clazz.getName.split("\\$\\$EnhancerByMockitoWithCGLIB\\$\\$")(0)
      clazz.getClassLoader.loadClass(originalName)
    } else
      clazz
  }

}
