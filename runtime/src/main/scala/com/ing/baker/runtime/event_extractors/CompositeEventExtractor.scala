package com.ing.baker.runtime.event_extractors

import com.ing.baker.runtime.core.RuntimeEvent
import com.typesafe.config.{Config, ConfigFactory}
import com.ing.baker.runtime.event_extractors.CompositeEventExtractor._

import scala.collection.JavaConverters._

object CompositeEventExtractor {

  private val classLoader = classOf[EventExtractor].getClassLoader

  def memoize[I, O](f: I => O): I => O = new scala.collection.mutable.HashMap[I, O]() {self =>
    override def apply(key: I) = self.synchronized(getOrElseUpdate(key, f(key)))
  }

  val memoizedExtractorInstance: Class[_] => EventExtractor = memoize {
    clazz => clazz.newInstance().asInstanceOf[EventExtractor]
  }

  /**
    * Loads all ingredient extractor bindings from a configuration.
    */
  def loadBindingsFromConfig(config: Config): Map[Class[_], EventExtractor] =

    config.getConfig("baker.event-extractor-bindings").entrySet().asScala.map {
      entry =>
        val extractorName = entry.getValue.unwrapped.asInstanceOf[String]
        val extractorClassName = config.getString(s"baker.event-extractors.$extractorName")
        val extractorClass = classLoader.loadClass(extractorClassName)
        val extractorInstance = memoizedExtractorInstance(extractorClass)
        val clazz = classLoader.loadClass(entry.getKey.stripPrefix("\"").stripSuffix("\""))
        clazz -> extractorInstance
    }.toMap
}

class CompositeEventExtractor(extractorBindings: Map[Class[_], EventExtractor]) extends EventExtractor {

  def this(config: Config) = this(loadBindingsFromConfig(config))

  def this() = this(ConfigFactory.load())

  /**
    * This finds the IngredientExtractor with a binding closest (in terms of class hierarchy) to the given class.
    */
  val extractorForClass = memoize[Class[_], EventExtractor] { clazz =>
    extractorBindings.keys.toSeq
      .filter(_.isAssignableFrom(clazz))
      .sortWith { (a, b) => b.isAssignableFrom(a) }
      .headOption
      .flatMap(extractorBindings.get)
      .getOrElse(throw new IllegalStateException(s"No suitable extractor found for $clazz"))
  }

  override def extractEvent(obj: Any): RuntimeEvent = extractorForClass(obj.getClass).extractEvent(obj)
}
