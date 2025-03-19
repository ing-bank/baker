package com.ing.baker.types

trait TypeLoader {

  protected[types] def removeType(name: String): Unit

  protected[types] def saveType(name: String, t: Type): Unit

  def loadType(name: String): Option[Type]
}

object TypeLoader {

  val defaultTypeLoader: TypeLoader = Converters.defaultTypeConverter
}
