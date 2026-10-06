package com.ing.baker.runtime.akka.internal

class FatalInteractionException(message: String, cause: Throwable = null) extends RuntimeException(message, cause)
