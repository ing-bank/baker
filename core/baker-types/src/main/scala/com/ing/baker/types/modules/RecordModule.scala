package com.ing.baker.types.modules

import com.ing.baker.types._

import java.lang.reflect.{Type => JType}

class RecordModule extends TypeModule {

  override def isApplicable(javaType: JType): Boolean = {
    try {
      getBaseClass(javaType).isRecord
    }
    catch {
      //if this happens, we don't use Java 16+
      case _: Exception => false
    }
  }

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {
    val recordType = getBaseClass(javaType)
    val ingredients: Seq[RecordField] = recordType.getRecordComponents.toIndexedSeq.map(f => RecordField(f.getName, context.readType(f.getGenericType)))
    RecordType(ingredients)
  }

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = value match {
    case NullValue => null
    case RecordValue(entries) =>
      val recordType = getBaseClass(javaType)

      val recordValues: Array[Any] = recordType.getRecordComponents
        .map(r => {
            val value = entries(r.getName)
            val fieldType = r.getGenericType
            try {
              context.toJava(value, fieldType)
            } catch {
              case e: Exception =>
                throw new IllegalStateException(s"Failed parse field '${r.getName}' as type: $fieldType", e)
            }
        })

      try {
        val paramTypes: Array[Class[_]] = recordType.getRecordComponents.map(r => r.getType)
        recordType.getDeclaredConstructors.find(constructor => {
          constructor.getParameterCount == paramTypes.length
        }) match {
          case Some(constructor) =>
            constructor.newInstance(recordValues: _*)
          case None =>
            throw new NoSuchMethodException("No constructor found for record")
        }
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
