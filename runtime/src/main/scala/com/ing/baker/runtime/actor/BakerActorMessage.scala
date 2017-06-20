package com.ing.baker.runtime.actor

import java.util.UUID

import io.kagera.akka.actor.PetriNetInstanceProtocol

case class BakerActorMessage(processId: UUID, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
