package com.ing.bakery.components

import cats.effect.IO
import com.ing.baker.runtime.model.InteractionInstance

case class RemoteInteractions(startedAt: Long,
                              interactions: List[InteractionInstance[IO]])
