package com.ing.baker.types.modules

import com.ing.baker.types._

import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType.methodType
import java.lang.reflect.{Type => JType}

class RecordModule extends TypeModule {

  private val LOOKUP = MethodHandles.lookup()
  override def isApplicable(javaType: JType): Boolean = {
    try {
      javaType.getClass.isRecord
    }
    catch {
      //if this happens, we don't use Java 16+
      case _: Exception => false
    }
  }

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {
    val recordType = getBaseClass(javaType)
    val ingredients = recordType.getRecordComponents.map(f => RecordField(f.getName, context.readType(f.getGenericType)))
    RecordType(ingredients)
  }

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = value match {
    case NullValue => null
    case RecordValue(entries) =>
      val recordType = getBaseClass(javaType)

      //
      val recordValues = recordType.getRecordComponents
        .map(r => {
            val value = entries(r.getName)
            val fieldType = r.getGenericType
            try {
              return context.toJava(value, fieldType)
            } catch {
              case e: Exception => throw new IllegalStateException(s"Failed parse field '${r.getName}' as type: $fieldType", e)
            }
        })

      try {
        val paramTypes = recordType.getRecordComponents.map(r => r.getType)
        val MH_canonicalConstructor = LOOKUP.findConstructor(recordType, methodType(classOf[Unit], paramTypes)).asType(methodType(classOf[AnyRef], paramTypes))
        MH_canonicalConstructor.invokeWithArguments(recordValues)

      } catch {
        case _: Exception =>
          throw new RuntimeException("Could not construct type (" + recordType.getName + ")")
      }

    case _=>
      throw new IllegalArgumentException(s"Unsupported value: $value")
  }

  override def fromJava(context: TypeAdapter, pojo: Any): Value = {
    val entries: Map[String, Value] = pojo.getClass.getRecordComponents
      .map(f => f.getName -> context.fromJava(f.getAccessor.invoke(pojo))).toMap //is order guaranteed?
    RecordValue(entries)
  }
}
