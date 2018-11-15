package com.ing.baker.il

import com.ing.baker.il.RecipeVisualizer.log
import com.typesafe.config.Config
import scalax.collection.io.dot.{DotAttr, DotAttrStmt, Elem}
import scala.collection.JavaConverters._
import scalax.collection.io.dot.implicits._

class RecipeVisualStyle(config: Config) {

  val visualizationConfig = config.getConfig("baker.visualization")
  val configuredStyle = visualizationConfig.getString("style")

  val pickedStyle = if (!visualizationConfig.hasPath(s"styles.$configuredStyle")) {
    log.warn(s"no configuration for recipe style '$configuredStyle' found, falling back to 'default' style")
    "default"
  } else
    configuredStyle

  val styleConfig = visualizationConfig.getConfig(s"styles.$pickedStyle")

  def readAttributes(keys: String*): List[DotAttr] = {
    val values = keys.foldLeft[Map[String, AnyRef]](Map.empty) {
      case (acc, key) =>
        val map = styleConfig.getConfig(key)
          .entrySet().asScala
          .map(e => e.getKey -> e.getValue.unwrapped())
        acc ++ map
    }

    values
      .-("shape") // shape is not allowed to be overriden
      .map {
      case (key, s: String) => Some(DotAttr(key, s))
      case (key, n: java.lang.Integer) => Some(DotAttr(key, n.intValue()))
      case (key, n: java.lang.Long) => Some(DotAttr(key, n.longValue()))
      case (key, n: java.lang.Float) => Some(DotAttr(key, n.floatValue()))
      case (key, n: java.lang.Double) => Some(DotAttr(key, n.doubleValue()))
      case (key, other) =>
        RecipeVisualizer.log.warn(s"unusable configuration: $key = $other");
        None
    }.toList.flatten
  }

  val rootAttributes = readAttributes("root")

  val commonNodeAttributes = List(
    DotAttrStmt(
      Elem.node,
      readAttributes("common")
    ))

  val ingredientAttributes: List[DotAttr] =
    DotAttr("shape", "circle") +: readAttributes("ingredient")

  val providedIngredientAttributes: List[DotAttr] =
    DotAttr("shape", "circle") +: readAttributes("ingredient", "fired")

  val missingIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  val eventAttributes: List[DotAttr] =
    DotAttr("shape", "diamond") +: readAttributes("event")

  val sensoryEventAttributes: List[DotAttr] =
    DotAttr("shape", "diamond") +: readAttributes("sensory-event")

  val interactionAttributes: List[DotAttr] =
    DotAttr("shape", "rect") +: readAttributes("interaction")

  val eventFiredAttributes: List[DotAttr] =
    DotAttr("shape", "diamond") +: readAttributes("event", "fired")

  val firedInteractionAttributes: List[DotAttr] =
    DotAttr("shape", "rect") +: readAttributes("interaction", "fired")

  val eventMissingAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  )

  val choiceAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.3),
    DotAttr("height", 0.3)
  )

  val emptyEventAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.1),
    DotAttr("height", 0.1)
  )

  val preconditionORAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("fontcolor", "black"),
    DotAttr("label", "OR"),
    DotAttr("style", "filled")
  )

  // this will be removed soon
  val sieveAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#7594d6\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )
}