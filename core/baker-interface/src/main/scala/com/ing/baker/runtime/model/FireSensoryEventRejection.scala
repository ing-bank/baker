package com.ing.baker.runtime.model

import com.ing.baker.runtime.common.RejectReason

sealed trait FireSensoryEventRejection {

  def asReason: RejectReason
}

object FireSensoryEventRejection {

  /**
    * Indicates that a process can no longer receive events because the configured period has expired.
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class ReceivePeriodExpired(recipeInstanceId: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.ReceivePeriodExpired
  }

  /**
    * @param msg error message for the request
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class InvalidEvent(recipeInstanceId: String, msg: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.InvalidEvent
  }

  /**
    * Returned if a process has been deleted
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class RecipeInstanceDeleted(recipeInstanceId: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.ProcessDeleted
  }

  /**
    * Returned if the process is uninitialized
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class NoSuchRecipeInstance(recipeInstanceId: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.NoSuchProcess
  }

  /**
    * The firing limit, the number of times this event may fire, was met.
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    */
  case class FiringLimitMet(recipeInstanceId: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.FiringLimitMet
  }

  /**
    * An event with the same correlation id was already received.
    *
    * @param recipeInstanceId The identifier of the RecipeInstanceId
    * @param correlationId The identifier used to secure uniqueness
    */
  case class AlreadyReceived(recipeInstanceId: String, correlationId: String) extends FireSensoryEventRejection {

    def asReason: RejectReason = RejectReason.AlreadyReceived
  }
}
