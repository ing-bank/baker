package com.ing.baker.runtime.core.events

import java.lang.reflect.Method

import com.ing.baker.runtime.core._
import org.slf4j.LoggerFactory

import scala.collection.immutable

class AnnotatedEventSubscriber(listener: AnyRef) extends PartialFunction[BakerEvent, Unit] {

  val log = LoggerFactory.getLogger(classOf[AnnotatedEventSubscriber])

  // Calculate the methods with @Subscribe annotation and also has exactly one argument which extends from BakerEvent
  val annotatedMethods: immutable.Seq[Method] = unmock(listener.getClass).getMethods.toList
    .filter(_.getAnnotationsByType(classOf[Subscribe]).nonEmpty)

  // validate one or more @Subscribe methods exist
  if (annotatedMethods.isEmpty) throw new IllegalArgumentException("BakerEventListener should have at least one @Subscribe annotated method")

  // validate the subscribeMethods extend from BakerEvent and also there's exactly one parameter
  annotatedMethods.foreach { m =>
    val clazz = m.getParameterTypes()(0)
    if (!classOf[BakerEvent].isAssignableFrom(clazz))
      throw new IllegalArgumentException("BakerEventListener methods cannot listen other types than BakerEvent")
    if (m.getParameterCount != 1)
      throw new IllegalArgumentException("BakerEventListener methods should have only one parameter")
  }

  // i.e. EventReceived.class -> List[listenerMethod]
  val mappedMethods: Map[Class[_], List[Method]] = annotatedMethods.foldLeft(Map.empty[Class[_], List[Method]]) {
    case (map, method) =>
      val parameterClass = method.getParameterTypes()(0)
      val previous = map.getOrElse(parameterClass, List.empty)
      map + (parameterClass -> (previous :+ method))
  }

  override def isDefinedAt(e: BakerEvent): Boolean = mappedMethods.keys.exists(clazz => isSubscribedToTheEvent(clazz, e.getClass))

  override def apply(e: BakerEvent): Unit = mappedMethods.foreach {
    case (subscribedClass, methods) if isSubscribedToTheEvent(subscribedClass, e.getClass) =>
      methods.foreach(_.invoke(listener, e))
    case _ => // Ignore other cases

  }

  private def isSubscribedToTheEvent(clazz: Class[_], eventClass: Class[_]): Boolean = clazz.isAssignableFrom(unmock(eventClass))
}
