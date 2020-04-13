package com.ing.baker.il

import com.typesafe.config.Config
import com.typesafe.scalalogging.LazyLogging
import scala.jdk.CollectionConverters._
import scalax.collection.io.dot.implicits._
import scalax.collection.io.dot.{ DotAttr, DotAttrStmt, Elem }

object RecipeVisualStyle extends LazyLogging {

  def default: RecipeVisualStyle = RecipeVisualStyle()

  def from(config: Config): RecipeVisualStyle = {

    val visualizationConfig = config.getConfig("baker.visualization")
    val configuredStyle = visualizationConfig.getString("style")
    val pickedStyle = if (!visualizationConfig.hasPath(s"styles.$configuredStyle")) {
      logger.warn(s"no configuration for recipe style '$configuredStyle' found, falling back to 'default' style")
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
            RecipeVisualizer.logger.warn(s"unusable configuration: $key = $other")
            None
        }.toList.flatten
    }

    RecipeVisualStyle(
      rootAttributes = readAttributes("root"),
      commonNodeAttributes = List(
        DotAttrStmt(
          Elem.node,
          readAttributes("common")
        )),
      ingredientAttributes =
        DotAttr("shape", "circle") +: readAttributes("ingredient"),
      providedIngredientAttributes =
        DotAttr("shape", "circle") +: readAttributes("ingredient", "fired"),
      eventAttributes =
        DotAttr("shape", "diamond") +: readAttributes("event"),
      sensoryEventAttributes =
        DotAttr("shape", "diamond") +: readAttributes("sensory-event"),
      interactionAttributes =
        DotAttr("shape", "rect") +: readAttributes("interaction"),
      eventFiredAttributes =
        DotAttr("shape", "diamond") +: readAttributes("event", "fired"),
      firedInteractionAttributes =
        DotAttr("shape", "rect") +: readAttributes("interaction", "fired")
    )
  }
}

case class RecipeVisualStyle(

  rootAttributes: List[DotAttr] = List(
    DotAttr("pad", 0.2)
  ),

  commonNodeAttributes: List[DotAttrStmt] = List(
    DotAttrStmt(
      Elem.node,
      List(
        DotAttr("fontname", "ING Me"),
        DotAttr("fontsize", 22),
        DotAttr("fontcolor", "white")
      )
    )
  ),

  ingredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
    DotAttr("color", "\"#FF6200\"")
  ),

  providedIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
    DotAttr("color", "\"#3b823a\"")
  ),

  missingIngredientAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("style", "filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  ),

  eventAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#767676\""),
    DotAttr("margin", 0.3D)
  ),

  sensoryEventAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#767676\""),
    DotAttr("fillcolor", "\"#D5D5D5\""),
    DotAttr("fontcolor", "black"),
    DotAttr("penwidth", 2),
    DotAttr("margin", 0.3D)
  ),

  interactionAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#525199\""),
    DotAttr("penwidth", 2),
    DotAttr("margin", 0.5D),
  ),

  eventFiredAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#3b823a\""),
    DotAttr("margin", 0.3D)
  ),

  firedInteractionAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#3b823a\""),
    DotAttr("penwidth", 2),
    DotAttr("margin", 0.5D),
  ),

  eventMissingAttributes: List[DotAttr] = List(
    DotAttr("shape", "diamond"),
    DotAttr("margin", 0.3D),
    DotAttr("style", "rounded, filled"),
    DotAttr("color", "\"#EE0000\""),
    DotAttr("penwidth", "5.0")
  ),

  choiceAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.3),
    DotAttr("height", 0.3)
  ),

  emptyEventAttributes: List[DotAttr] = List(
    DotAttr("shape", "point"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("width", 0.1),
    DotAttr("height", 0.1)
  ),

  preconditionORAttributes: List[DotAttr] = List(
    DotAttr("shape", "circle"),
    DotAttr("fillcolor", "\"#D0D93C\""),
    DotAttr("fontcolor", "black"),
    DotAttr("label", "OR"),
    DotAttr("style", "filled")
  ),

  // this will be removed soon
  sieveAttributes: List[DotAttr] = List(
    DotAttr("shape", "rect"),
    DotAttr("margin", 0.5D),
    DotAttr("color", "\"#7594d6\""),
    DotAttr("style", "rounded, filled"),
    DotAttr("penwidth", 2)
  )
)
