package com.ing.baker.types.modules

import com.ing.baker.types._
import org.joda.time.{DateTime, LocalDate, ReadableInstant}

class JodaTimeModule extends TypeModule {

  val baseClass = classOf[ReadableInstant]

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean = ???

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = ???

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = ???

  override def fromJava(context: TypeAdapter, obj: Any): Value = ???

//  obj match {
//
//    case dateTime: DateTime => PrimitiveValue(dateTime.getMillis)
//    case localDate: LocalDate => PrimitiveValue(localDate.get)
//  }
}
