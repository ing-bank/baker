package com.ing.baker.core

class BakerException(message: String = "An exception occured at Baker", cause: Throwable = null)
    extends RuntimeException(message, cause)
