package com.ing.baker.runtime.actor

import akka.actor.ExtendedActorSystem
import akka.persistence.journal.{EventAdapter, EventSeq}
import com.ing.baker.runtime._

class BakerEventAdapter(system: ExtendedActorSystem) extends EventAdapter {

  override def manifest(event: Any): String = "" // not needed

  override def toJournal(event: Any): Any = event match {
    case e: core.RuntimeEvent => toProtoMessage(e)
    case e: core.ProcessState => toProtoMessage(e)
  }

  override def fromJournal(event: Any, manifest: String): EventSeq = event match {
    case e: messages.RuntimeEvent => EventSeq.single(toDomainMessage(e))
    case e: messages.ProcessState => EventSeq.single(toDomainMessage(e))
  }

  private def toProtoMessage(runtimeEvent: core.RuntimeEvent): messages.RuntimeEvent = ???

  private def toProtoMessage(processState: core.ProcessState): messages.RuntimeEvent = ???

  def toDomainMessage(e: messages.RuntimeEvent): core.RuntimeEvent = ???

  def toDomainMessage(e: messages.ProcessState): core.ProcessState = ???

}
