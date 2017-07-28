package com.ing.baker.runtime.actor

import java.util.UUID

import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol

case class BakerActorMessage(processId: UUID, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
