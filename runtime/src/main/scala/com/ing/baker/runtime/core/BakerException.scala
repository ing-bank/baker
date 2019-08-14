package com.ing.baker.runtime.core

class BakerException(message: String = "An exception occurred at Baker", cause: Throwable = null)
    extends RuntimeException(message, cause)
