package com.ing.baker.recipe

import java.lang.reflect.{Modifier, ParameterizedType, Type}

import scala.reflect.runtime.{universe => ru}

package object common {
  val ProcessIdName = "$ProcessId$"

  val mirror: ru.Mirror = ru.runtimeMirror(classOf[IngredientType].getClassLoader)

  // TODO should be string identifier instead
  val supportedPrimitiveClasses: Set[Class[_]] = Set(
    java.lang.Boolean.TYPE,
    java.lang.Byte.TYPE,
    java.lang.Short.TYPE,
    java.lang.Character.TYPE,
    java.lang.Integer.TYPE,
    java.lang.Long.TYPE,
    java.lang.Float.TYPE,
    java.lang.Double.TYPE,
    classOf[java.lang.Boolean],
    classOf[java.lang.Byte],
    classOf[java.lang.Short],
    classOf[java.lang.Character],
    classOf[java.lang.Integer],
    classOf[java.lang.Long],
    classOf[java.lang.Float],
    classOf[java.lang.Double],
    classOf[java.lang.String],
    classOf[java.math.BigDecimal],
    classOf[java.math.BigInteger],
    classOf[org.joda.time.DateTime],
    classOf[org.joda.time.LocalDate],
    classOf[org.joda.time.LocalDateTime]
  )

  def asJavaType(paramType: ru.Type): java.lang.reflect.Type = {
    val typeConstructor = mirror.runtimeClass(paramType)
    val innerTypes = paramType.typeArgs.map(asJavaType).toArray

    if (innerTypes.isEmpty) {
      typeConstructor
    } else {
      new java.lang.reflect.ParameterizedType {
        override def getRawType: java.lang.reflect.Type = typeConstructor
        override def getActualTypeArguments: Array[java.lang.reflect.Type] = innerTypes
        override def getOwnerType: java.lang.reflect.Type = null
        override def toString() = s"ParameterizedType: $typeConstructor[${getActualTypeArguments.mkString(",")}]"
      }
    }
  }

  def getRawClass(t: Type): Class[_] = t match {
    case c: Class[_] => c
    case t: ParameterizedType => getRawClass(t.getRawType)
    case t@_ => throw new IllegalArgumentException(s"Unsupported type: $t")
  }

  def makeType[T : ru.TypeTag]: java.lang.reflect.Type = {
    asJavaType(ru.typeOf[T])
  }

  def ingredientTypeFromType(clazz: Type): IngredientType = {

    clazz match {
      case clazz: Class[_] if supportedPrimitiveClasses.contains(clazz) =>
        PrimitiveType(clazz)
      case clazz: ParameterizedType if classOf[scala.Option[_]].isAssignableFrom(getRawClass(clazz)) || classOf[java.util.Optional[_]].isAssignableFrom(getRawClass(clazz)) =>
        val entryType = ingredientTypeFromType(clazz.getActualTypeArguments()(0))
        OptionType(entryType)
      case clazz: ParameterizedType if getRawClass(clazz.getRawType).isAssignableFrom(classOf[List[_]]) || getRawClass(clazz.getRawType).isAssignableFrom(classOf[java.util.List[_]]) =>
        val entryType = ingredientTypeFromType(clazz.getActualTypeArguments()(0))
        ListType(entryType)
      case enumClass: Class[_] if enumClass.isEnum =>
        EnumType(enumClass.asInstanceOf[Class[Enum[_]]].getEnumConstants.map(_.name).toSet)
      case pojoClass: Class[_] =>
        val fields = pojoClass.getDeclaredFields.filterNot(f => f.isSynthetic || Modifier.isStatic(f.getModifiers))
        val ingredients = fields.map(f => new Ingredient(f.getName, ingredientTypeFromType(f.getGenericType)))
        POJOType(ingredients)
      case unsupportedType =>
        throw new IllegalArgumentException(s"UnsupportedType: $unsupportedType")
    }
  }
}
