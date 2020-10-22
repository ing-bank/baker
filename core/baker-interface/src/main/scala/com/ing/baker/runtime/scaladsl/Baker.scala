package com.ing.baker.runtime.scaladsl

import scala.concurrent.Future

/**
  * The Baker is the component of the Baker library that runs one or multiples recipes.
  * For each recipe a new instance can be baked, sensory events can be send and state can be inquired upon
  */
trait Baker extends BakerF[Future]
