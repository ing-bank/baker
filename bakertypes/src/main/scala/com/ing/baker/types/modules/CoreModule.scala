package com.ing.baker.types.modules

import java.lang.reflect
import java.lang.reflect.ParameterizedType
import java.util.Optional

import com.ing.baker.types
import com.ing.baker.types.Converters.getBaseClass
import com.ing.baker.types._

class CoreModule extends TypeModule {

  private def isEmpty(obj: Any) = {
    obj match {
      case None => true
      case option: java.util.Optional[_] if !option.isPresent => true
      case _ => false
    }
  }

  override def isApplicable(javaType: reflect.Type): Boolean = true

  override def readType(context: TypeConverter, javaType: java.lang.reflect.Type): Type = {

    javaType match {
      case clazz if clazz == classOf[Object] =>
        throw new IllegalArgumentException(s"Unsupported type: $clazz")
      case clazz: Class[_] if primitiveMappings.contains(clazz) =>
        primitiveMappings(clazz)
      case clazz: ParameterizedType if classOf[scala.Option[_]].isAssignableFrom(getBaseClass(clazz)) || classOf[java.util.Optional[_]].isAssignableFrom(getBaseClass(clazz)) =>
        val entryType = context.readType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
      case t: ParameterizedType if classOf[scala.Array[_]].isAssignableFrom(getBaseClass(t)) && classOf[Byte].isAssignableFrom(getBaseClass(t.getActualTypeArguments()(0))) =>
        types.ByteArray

      case enumClass: Class[_] if enumClass.isEnum =>
        EnumType(enumClass.asInstanceOf[Class[Enum[_]]].getEnumConstants.map(_.name).toSet)

      case unsupportedType =>
        throw new IllegalArgumentException(s"UnsupportedType: $unsupportedType")
    }
  }


  /**
    * Attempts to convert a java object to a value.
    *
    * @param obj The java object
    * @return a Value
    */
  override def fromJava(context: TypeConverter, obj: Any): Value = {

    obj match {
      case value if isEmpty(value)          => NullValue

      case Some(optionValue)                => context.fromJava(optionValue)
      case option: java.util.Optional[_] if option.isPresent => context.fromJava(option.get)
      case enum if enum.getClass.isEnum     => PrimitiveValue(enum.asInstanceOf[Enum[_]].name())
    }
  }

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    *
    * @return An instance of the java type.
    */
  @throws[IllegalArgumentException]("If failing to convert to the desired java type")
  override def toJava(context: TypeConverter, value: Value, javaType: java.lang.reflect.Type): Any = {

    (value, javaType) match {
      case (_, clazz) if clazz == classOf[Object] =>
        throw new IllegalArgumentException(s"Unsupported type: $clazz")

      case (primitive: PrimitiveValue, clazz: Class[_]) if primitive.isAssignableTo(clazz) =>
        primitive.value

      case (PrimitiveValue(option: String), clazz: Class[_]) if clazz.isEnum =>
        clazz.asInstanceOf[Class[Enum[_]]].getEnumConstants.find(_.name() == option) match {
          case Some(enumValue) => enumValue
          case None => throw new IllegalArgumentException(s"value '$option' is not an instance of enum: $clazz")
        }

      case (_, generic: ParameterizedType) if classOf[Option[_]].isAssignableFrom(getBaseClass(generic.getRawType)) =>
        val optionType = generic.getActualTypeArguments()(0)
        value match {
          case NullValue =>
            None
          case _ =>
            val optionValue = context.toJava(value, optionType)
            Some(optionValue)
        }

      case (_, generic: ParameterizedType) if classOf[java.util.Optional[_]].isAssignableFrom(getBaseClass(generic.getRawType)) =>
        val optionType = generic.getActualTypeArguments()(0)

        value match {
          case NullValue =>
            Optional.empty()
          case _ =>
            val optionValue = context.toJava(value, optionType)
            java.util.Optional.of(optionValue)
        }

      case (NullValue, _) =>
        null
    }
  }
}
