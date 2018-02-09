package com.ing.baker.types

import java.nio.charset.StandardCharsets
import java.util

import scala.reflect.runtime.universe
import scala.util.Try

sealed trait Value extends Serializable {

  def isNull: Boolean = this == NullValue

  def isInstanceOf(t: Type): Boolean = (t, this) match {
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

  def equalsObject(obj: Any): Boolean = Try { equals(Converters.toValue(obj)) }.getOrElse(false)
}

/**
  * Indicates the absence of a value.
  *
  * null, void, none, empty, etc...
  *
  */
case object NullValue extends Value {

  override def toString: String = "null"
}

// should inherit AnyVal
case class PrimitiveValue(value: Any) extends Value {
  if (!isPrimitiveValue(value))
    throw new IllegalArgumentException(s"value is not supported: $value")

  def isAssignableTo(clazz: Class[_]) =
    (supportedPrimitiveClasses.contains(clazz) && clazz.isInstance(value)) ||
      (clazz.isPrimitive && javaPrimitiveMappings.get(value.getClass).contains(clazz))

  override def toString: String = value match {
    case str: String                         => "\"" + str + "\""
    case date: org.joda.time.ReadableInstant => "\"" + isoDateTimeFormatter.print(date) + "\""
    case n: java.math.BigDecimal             => "\"" + n.toString + "\""
    case n: java.math.BigInteger             => "\"" + n.toString + "\""
    case n: BigDecimal                       => "\"" + n.toString + "\""
    case n: BigInt                           => "\"" + n.toString + "\""
    case bytes: Array[_]                     =>
      val str = new String(bytes.asInstanceOf[Array[Byte]], StandardCharsets.UTF_8)
      "\"" + str + "\""

    case other => other.toString
  }

  override def equals(obj: Any): Boolean = {
    obj match {
      case null => false
      case PrimitiveValue(bytes: Array[_]) if value.getClass.isArray =>
        util.Arrays.equals(bytes.asInstanceOf[Array[Byte]], value.asInstanceOf[Array[Byte]])
      case PrimitiveValue(otherValue) => otherValue.equals(value)
      case _ => false
    }
  }

  override def hashCode(): Int = {
    // Picking here a prime number multiplier other than 31 (used by the standard hashCode implementations)
    // This reduces the chance that this holds true: "test".hashCode() == PrimitiveValue("test").hashCode()
    if (value.getClass.isArray) {
      util.Arrays.hashCode(value.asInstanceOf[Array[Byte]]) * 101
    } else {
      value.hashCode() * 101
    }
  }

}

case class RecordValue(entries: Map[String, Value]) extends Value {

  override def toString: String = entries.map { case (name, value) => "\"" + name + "\" : " + value  }.mkString("{", ",", "}")
}

case class ListValue(entries: List[Value]) extends Value {

  override def toString: String = entries.mkString("[", ",", "]")
}
