package com.ing.baker.runtime.core

class BakerException(message: String = "An exception occured at Baker", cause: Throwable = null)
    extends RuntimeException(message, cause)
