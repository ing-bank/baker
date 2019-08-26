package com.ing.baker.runtime.akka.actor.interaction_agent

import com.ing.baker.types.Type

case class InteractionAgentDescriptor(
   name: String,
   input: Seq[Type],
   output: Option[Map[String, Map[String, Type]]])
