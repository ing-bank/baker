package com.ing.baker.runtime.core

import com.ing.baker.types.{Converters, RecordValue}

import scala.concurrent.Future
import scala.language.postfixOps

object Baker {

  /**
    * Transforms an object into a RuntimeEvent if possible.
    */
  def extractEvent(event: Any): RuntimeEvent = {
    // transforms the given object into a RuntimeEvent instance
    event match {
      case runtimeEvent: RuntimeEvent => runtimeEvent
      case obj =>
        Converters.toValue(obj) match {
          case RecordValue(entries) => RuntimeEvent(obj.getClass.getSimpleName, entries.toSeq)
          case other => throw new IllegalArgumentException(s"Unexpected value: $other")
        }
    }
  }
}

//A Baker using the Scala collection types
trait ScalaBaker[F[_]] extends BakerInterface[F, Map, Seq, Set]

//A Baker using the Java collection types
trait JavaBaker[F[_]] extends BakerInterface[F, java.util.Map, java.util.List, java.util.Set]

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends ScalaBaker[Future]
