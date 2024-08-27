package com.ing.baker.types.modules

import com.ing.baker.types._

import java.lang.reflect.{Type => JType}
import java.time.Duration

/**
  * This module is using POJO representation for the Duration instead of the Date.
  * This is done to ensure backwards compatibility.
  * In older versions Durations are translated to our POJO type but in Java 17 the initialization from POJO to Duration does not work anymore.
  */
class DurationModule extends TypeModule {

  override def isApplicable(javaType: JType): Boolean =
    isAssignableToBaseClass(javaType, classOf[Duration])

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {
    RecordType(Seq(RecordField("seconds", Int64), RecordField("nanos", Int32)))
  }

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any =
    (value, javaType) match {
      case (NullValue, _) => null
      case (RecordValue(entries), clazz: Class[_]) if classOf[Duration].isAssignableFrom(clazz) =>
        val seconds: Long = entries("seconds").as[Long]
        val nanos: Int = entries("nanos").as[Int]
        Duration.ofSeconds(seconds).withNanos(nanos)
      case _=>
        throw new IllegalArgumentException(s"Unsupported value: $value")
  }

  override def fromJava(context: TypeAdapter, obj: Any): Value = {
    obj match {
      case duration: Duration =>
        val seconds: Long = duration.getSeconds
        val nanos: Int = duration.getNano
        RecordValue(Map("seconds" -> Converters.toValue(seconds), "nanos" -> Converters.toValue(nanos)))
      case _ =>
        throw new IllegalArgumentException(s"Could not translate from Java object")
    }
  }
}
