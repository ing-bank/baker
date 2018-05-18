package com.ing.baker.petrinet.runtime

import com.ing.baker.petrinet.api.MultiSet

trait ExceptionHandler[P[_], T[_], S] {

  def handleException(job: Job[P, T, S])(throwable: Throwable,
                                         failureCount: Int,
                                         startTime: Long,
                                         outMarking: MultiSet[P[_]]): ExceptionStrategy
}
