package com.ing.baker.runtime.actor

import com.ing.baker.petrinet.akka.PetriNetInstanceProtocol

case class BakerActorMessage(processId: String, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
