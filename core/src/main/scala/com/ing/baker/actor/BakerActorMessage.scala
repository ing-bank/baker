package com.ing.baker.actor

import java.util.UUID

import io.kagera.akka.actor.PetriNetInstanceProtocol

case class BakerActorMessage(processId: UUID, cmd: PetriNetInstanceProtocol.Command) extends InternalBakerMessage
