package com.ing.baker.types.modules

import java.lang.reflect.Modifier
import com.ing.baker.types._
import org.objenesis.ObjenesisStd

import scala.util.{Failure, Success, Try}

class PojoModule extends TypeModule {

  override def isApplicable(javaType: java.lang.reflect.Type): Boolean = true

  override def readType(context: TypeAdapter, javaType: java.lang.reflect.Type): Type = {

    val pojoClass = getBaseClass(javaType)
    val className = pojoClass.getName

    context.loadType(className) match {
      case Some(t) => t
      case _       =>
        Try {
          // we save the type as a reference type to avoid recursion
          context.saveType(className, ReferenceType(context, className));

          val fields = pojoClass.getDeclaredFields.toIndexedSeq.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))
          val ingredients = fields.map(f => RecordField(f.getName, context.readType(f.getGenericType)))
          val `type` = RecordType(ingredients)
          context.saveType(className, `type`);
          RecordType(ingredients)

        } match {

          case Failure(e) =>
            context.removeType(className)
            throw e
          case Success(result) =>
            context.saveType(className, result);
            result
        }
    }
  }

  override def toJava(context: TypeAdapter, value: Value, javaType: java.lang.reflect.Type): Any = value match {
    case NullValue => null
    case RecordValue(entries) =>

      val pojoClass = getBaseClass(javaType)

      // ObjenesisStd is somehow bypassing the constructor
      val objenesis = new ObjenesisStd // or ObjenesisSerializer

      val classInstantiator = objenesis.getInstantiatorOf(pojoClass)

      val pojoInstance = classInstantiator.newInstance()

      val fields = pojoClass.getDeclaredFields.toIndexedSeq.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))

      fields.foreach { f =>
        entries.get(f.getName).foreach { entryValue =>

          val fieldType = f.getGenericType()
          try {
            val value = context.toJava(entryValue, fieldType)
            f.setAccessible(true)
            f.set(pojoInstance, value)
          } catch {
            case e: Exception => throw new IllegalStateException(s"Failed parse field '${f.getName}' as type: $fieldType", e)
          }
        }
      }

      pojoInstance

    case _=>
      throw new IllegalArgumentException(s"Unsupported value: $value")
  }

  override def fromJava(context: TypeAdapter, pojo: Any): Value = {
    val fields = pojo.getClass.getDeclaredFields.toIndexedSeq.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))
    fields.foreach(_.setAccessible(true))

    val entries: Map[String, Value] = fields
      .map(f => f.getName -> context.fromJava(f.get(pojo))).toMap

    RecordValue(entries)
  }
}
