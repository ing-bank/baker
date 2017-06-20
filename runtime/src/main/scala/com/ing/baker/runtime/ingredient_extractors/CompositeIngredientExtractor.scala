package com.ing.baker.runtime.ingredient_extractors

import com.typesafe.config.{Config, ConfigFactory}
import com.ing.baker.runtime.ingredient_extractors.CompositeIngredientExtractor._

import scala.collection.JavaConverters._

object CompositeIngredientExtractor {

  private val classLoader = classOf[IngredientExtractor].getClassLoader

  def memoize[I, O](f: I => O): I => O = new scala.collection.mutable.HashMap[I, O]() {self =>
    override def apply(key: I) = self.synchronized(getOrElseUpdate(key, f(key)))
  }

  val memoizedExtractorInstance: Class[_] => IngredientExtractor = memoize {
    clazz => clazz.newInstance().asInstanceOf[IngredientExtractor]
  }

  /**
    * Loads all ingredient extractor bindings from a configuration.
    */
  def loadBindingsFromConfig(config: Config): Map[Class[_], IngredientExtractor] =

    config.getConfig("baker.ingredient-extractor-bindings").entrySet().asScala.map {
      entry =>
        val extractorName = entry.getValue.unwrapped.asInstanceOf[String]
        val extractorClassName = config.getString(s"baker.ingredient-extractors.$extractorName")
        val extractorClass = classLoader.loadClass(extractorClassName)
        val extractorInstance = memoizedExtractorInstance(extractorClass)
        val clazz = classLoader.loadClass(entry.getKey.stripPrefix("\"").stripSuffix("\""))
        clazz -> extractorInstance
    }.toMap
}

class CompositeIngredientExtractor(extractorBindings: Map[Class[_], IngredientExtractor]) extends IngredientExtractor {

  def this(config: Config) = this(loadBindingsFromConfig(config))

  def this() = this(ConfigFactory.load())

  /**
    * This finds the IngredientExtractor with a binding closest (in terms of class hierarchy) to the given class.
    */
  val extractorForClass = memoize[Class[_], IngredientExtractor] { clazz =>
    extractorBindings.keys.toSeq
      .filter(_.isAssignableFrom(clazz))
      .sortWith { (a, b) => b.isAssignableFrom(a) }
      .headOption
      .flatMap(extractorBindings.get)
      .getOrElse(throw new IllegalStateException(s"No suitable extractor found for $clazz"))
  }

  override def extractIngredientTypes(clazz: Class[_]): Map[String, Class[_]] =
    extractorForClass(clazz).extractIngredientTypes(clazz)

  override def extractIngredientData(obj: Any): Map[String, Any] =
    extractorForClass(obj.getClass).extractIngredientData(obj)
}
