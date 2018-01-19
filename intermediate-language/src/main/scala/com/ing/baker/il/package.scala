package com.ing.baker

import java.lang.reflect.{ParameterizedType, Type}
import java.security.MessageDigest
import java.util.Optional

import com.ing.baker.il.ActionType.{InteractionAction, SieveAction}
import com.ing.baker.il.petrinet.Place._
import com.ing.baker.il.petrinet.{EventTransition, InteractionTransition, MissingEventTransition, MultiFacilitatorTransition, Place, Transition}
import com.ing.baker.types.RecordField


package object il {

  val processIdName = "$ProcessID$"

  type IngredientDescriptor = RecordField

  implicit class PlaceAdditions(place: Place[_]) {
    def isIngredient: Boolean = place.placeType == IngredientPlace

    def isInteractionEventOutput: Boolean = place.placeType == InteractionEventOutputPlace

    def isFiringLimiter: Boolean = place.placeType.isInstanceOf[FiringLimiterPlace]

    def isEventPrecondition: Boolean = place.placeType == EventPreconditionPlace

    def isOrEventPrecondition: Boolean = place.placeType == EventOrPreconditionPlace

    def isIntermediate: Boolean = place.placeType == IntermediatePlace

    def isEmptyEventIngredient: Boolean = place.placeType == EmptyEventIngredientPlace
  }

  implicit class TransitionAdditions(transition: Transition[_, _]) {

    def isInteraction: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == InteractionAction
    }

    def isMultiFacilitatorTransition: Boolean = transition.isInstanceOf[MultiFacilitatorTransition]

    def isSieve: Boolean = PartialFunction.cond(transition) {
      case t: InteractionTransition[_] => t.actionType == SieveAction
    }

    def isEventMissing: Boolean = transition.isInstanceOf[MissingEventTransition[_]]

    def isSensoryEvent: Boolean =
      transition match {
      case EventTransition(_, true, _) => true
      case _ => false
    }
  }

  def sha256HashCode(str: String): Long = {
    val sha256Digest: MessageDigest = MessageDigest.getInstance("SHA-256")
    BigInt(1, sha256Digest.digest(str.getBytes("UTF-8"))).toLong
  }

  def getRawClass(t: Type): Class[_] = t match {
    case c: Class[_] => c
    case t: ParameterizedType => getRawClass(t.getRawType)
    case t@_ => throw new IllegalArgumentException(s"Unsupported type: $t")
  }

  /**
    * These are the types that can be auto-boxed by baker.
    *
    * Example: If an ingredient of Option[String] is expected, but String is provided
    * it will be boxed as Option[String]
    */
  val autoBoxClasses = Map[Class[_], Any => Any](
    classOf[Option[_]] -> (unboxed => Some(unboxed)),
    classOf[Optional[_]] -> (unboxed => java.util.Optional.of(unboxed))
  )

  /**
    * other should be assignable to self
    *
    * @return
    */
  def isAssignableFromType(self: Type, other: Type): Boolean = {
    self match {
      case c: Class[_] =>
        c.isAssignableFrom(getRawClass(other))
      case p: ParameterizedType =>

        val check = other match {
          case otherP: ParameterizedType =>
            isAssignableFromType(p.getRawType, otherP.getRawType) &&
              p.getActualTypeArguments.zip(otherP.getActualTypeArguments).map {
                case (a, b) => isAssignableFromType(a, b)
              }.forall(_ == true)
          case _ => false
        }
        if (!check && autoBoxClasses.contains(getRawClass(p.getRawType)))
          isAssignableFromType(p.getActualTypeArguments.apply(0), other)
        else check
      case _ => false
    }
  }
}
