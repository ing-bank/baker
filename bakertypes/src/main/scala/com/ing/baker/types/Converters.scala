package com.ing.baker.types

import com.typesafe.config.ConfigFactory
import org.slf4j.LoggerFactory

import scala.collection.JavaConverters._
import scala.reflect.runtime.universe
import scala.reflect.runtime.universe.TypeTag

object Converters {

  private val log = LoggerFactory.getLogger("com.ing.baker.types")

  def loadDefaultModulesFromConfig(): Map[Class[_], TypeModule] = {
    val defaultConfig = ConfigFactory.load()

    defaultConfig.getConfig("baker.types").entrySet().asScala.map {
      entry =>

        def stripQuotes(str: String) = str.stripPrefix("\"").stripSuffix("\"")

        try {

          val moduleClassName = stripQuotes(entry.getValue.unwrapped.asInstanceOf[String])
          val className = stripQuotes(entry.getKey)

          val clazz = classOf[Value].getClassLoader().loadClass(className)
          val moduleClass = classOf[Value].getClassLoader().loadClass(moduleClassName)
          val module = moduleClass.newInstance().asInstanceOf[TypeModule]

          Some(clazz -> module)
        }
        catch {
          case e: Exception =>
            log.error("Failed to load type module: ", e)
            None
        }
    }.collect {
      case Some(entry) => entry
    }.toMap[Class[_], TypeModule]
  }

  val defaultTypeConverter = new TypeAdapter(loadDefaultModulesFromConfig())

  def readJavaType[T : TypeTag]: Type = readJavaType(createJavaType(mirror.typeOf[T]))

  def readJavaType(javaType: java.lang.reflect.Type): Type = defaultTypeConverter.readType(javaType)

  /**
    * Attempts to convert a java object to a value.
    *
    * @param obj The java object
    * @return a Value
    */
  def toValue(obj: Any): Value = defaultTypeConverter.fromJava(obj)

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @param javaType The desired java type.
    *
    * @return An instance of the java type.
    */
  @throws[IllegalArgumentException]("If failing to convert to the desired java type")
  def toJava(value: Value, javaType: java.lang.reflect.Type): Any = defaultTypeConverter.toJava(value, javaType)

  /**
    * Attempts to convert a value to a desired java type.
    *
    * @param value    The value
    * @return An instance of the java type.
    */
  @throws[IllegalArgumentException]("If failing to convert to the desired java type")
  def toJava[T : universe.TypeTag](value: Value): T = toJava(value, createJavaType(universe.typeOf[T])).asInstanceOf[T]
}
