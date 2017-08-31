package com.ing.baker.runtime.actor

case class BakerActorMessage(processId: String, cmd: ProcessInstanceProtocol.Command) extends InternalBakerMessage
