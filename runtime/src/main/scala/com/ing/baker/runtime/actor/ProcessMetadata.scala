package com.ing.baker.runtime.actor

/**
  * This class is to store some metadata information of a baker process
  *
  * @param id process id
  * @param createdTime process created date-time
  */
case class ProcessMetadata(id: String, createdTime: Long)
