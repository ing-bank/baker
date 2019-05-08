package com.ing.baker.runtime.common

/**
  * Thrown when attempting to act or inquire on an already deleted process.
  *
  * @param msg
  */
class ProcessDeletedException(msg: String) extends BakerException(msg)
