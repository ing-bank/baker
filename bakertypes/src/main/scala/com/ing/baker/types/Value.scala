package com.ing.baker.types

import scala.reflect.runtime.universe

sealed trait Value extends Serializable {

  def isNull: Boolean = this == NullValue

  def isInstanceOf(t: BType): Boolean = (t, this) match {
    case (_, NullValue)                                     => true
    case (PrimitiveType(clazz), v: PrimitiveValue)          => v.isAssignableTo(clazz)
    case (ListType(entryType), ListValue(entries))          => entries.forall(_.isInstanceOf(entryType))
    case (OptionType(entryType), v: Value)                  => v.isInstanceOf(entryType)
    case (EnumType(options), PrimitiveValue(value: String)) => options.contains(value)
    case (RecordType(entryTypes), RecordValue(entryValues)) => entryTypes.forall { f =>
      entryValues.get(f.name) match {
        case None        => false
        case Some(value) => value.isInstanceOf(f.`type`)
      }
    }
    case (MapType(valueType), RecordValue(entries))         => entries.values.forall(_.isInstanceOf(valueType))
    case _ => false
  }

  def as(javaType: java.lang.reflect.Type): Any = Converters.toJava(this, javaType)

  def as[T](clazz: Class[T]): T = Converters.toJava(this, clazz).asInstanceOf[T]

  def as[T : universe.TypeTag]: T = Converters.toJava[T](this)
}

/**
  * Indicates the absence of a value.
  *
  * null, void, none, empty, etc...
  *
  */
case object NullValue extends Value {

  override def toString(): String = "null"
}

// should inherit AnyVal
case class PrimitiveValue(value: Any) extends Value {
  if (!isPrimitiveValue(value))
    throw new IllegalArgumentException(s"value is not supported: $value")

  def isAssignableTo(clazz: Class[_]) =
    (supportedPrimitiveClasses.contains(clazz) && clazz.isInstance(value)) ||
      (clazz.isPrimitive && javaPrimitiveMappings.get(value.getClass) == Some(clazz))

  override def toString(): String = value.toString
}

case class RecordValue(entries: Map[String, Value]) extends Value {

  override def toString(): String = entries.map   { case (name, value) => "\"" + name + "\" : " + value  }.mkString("{", ",", "}")
}

case class ListValue(entries: List[Value]) extends Value {

  override def toString(): String = entries.mkString("[", ",", "]")
}
