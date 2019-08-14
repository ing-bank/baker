package com.ing.baker.runtime.core

/**
  * Thrown when attempting to act or inquire on an already deleted process.
  *
  * @param msg
  */
class ProcessDeletedException(msg: String) extends BakerException(msg)
