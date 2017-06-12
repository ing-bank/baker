package com.ing.baker.runtime.core

class FatalBakerException(message: String = "An exception occured at Baker", cause: Throwable = null)
  extends RuntimeException(message, cause)
