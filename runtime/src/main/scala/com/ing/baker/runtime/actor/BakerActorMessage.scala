package com.ing.baker.runtime.actor

import io.kagera.akka.actor.PetriNetInstanceProtocol

case class BakerActorMessage(processId: String, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
