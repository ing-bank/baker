package com.ing.baker.newrecipe.common

/**
  * A Recipe combines a set of interactions & events.
  */
trait Recipe {

  /**
    * The name of the recipe.
    */
  val name: String

  /**
    * The set of interactions.
    */
  val interactions: Seq[InteractionDescriptor]

  /**
    * The set of sieves.
    */
  val sieves: Seq[InteractionDescriptor]

  /**
    * The set of events.
    */
  val events: Set[Event]


  override def toString: String = {
    val appender = "  "
    val appender2 = appender + appender
    s"""{
        |  Recipe: $name
        |  Interactions:{
        |${interactions.foldLeft("")((i, j) => s"$i\n${j.toString(appender2)}").replaceFirst("\n", "")}
        |  }
        |  Sieves:{
        |${sieves.foldLeft("")((i, j) => s"$i\n${j.toString(appender2)}").replaceFirst("\n", "")}
        |  }
        |  Events:{
        |${events.foldLeft("")((i, j) => s"$i\n${j.toString(appender2)}").replaceFirst("\n", "")}
        |  }
        |}
        |""".stripMargin
  }
}
