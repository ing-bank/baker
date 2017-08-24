package com.ing.baker.runtime.actor

case class BakerActorMessage(processId: String, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
