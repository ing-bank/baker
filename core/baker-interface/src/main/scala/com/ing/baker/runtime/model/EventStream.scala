package com.ing.baker.runtime.model

import com.ing.baker.runtime.scaladsl.BakerEvent

import scala.util.Try

trait EventStream {

  protected def fetchListeners: List[BakerEvent => Unit]

  def subscribe(listenerFunction: BakerEvent => Unit): Unit

  def publish[F[_]](event: BakerEvent)(implicit components: BakerComponents[F]): Unit = {
    fetchListeners.foreach(listener =>
      Try(listener(event))
        .recover { case e => components.logging.exceptionOnEventListener(e) }
    )
  }
}