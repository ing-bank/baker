package com.ing.baker.recipe.javadsl

import com.ing.baker.recipe.common
import com.ing.baker.recipe.common.InteractionFailureStrategy.RetryWithIncrementalBackoff.{UntilDeadline, UntilMaximumRetries, Until}
import com.ing.baker.recipe.common.InteractionFailureStrategy.{BlockInteraction, RetryWithIncrementalBackoff}

import scala.concurrent.duration.{Duration, MILLISECONDS}

object InteractionFailureStrategy {

  case class RetryWithIncrementalBackoffBuilder private(private val initialDelay: Option[java.time.Duration],
                                                        private val backoffFactor: Double,
                                                        private val until: Option[Until],
                                                        private val maxTimeBetweenRetries: Option[java.time.Duration],
                                                        private val fireRetryExhaustedEvent: Option[Option[String]],
                                                        private val fireFunctionalEvent: Option[Option[String]]) {
    // initialize with defaults
    def this() = this(initialDelay = None, backoffFactor = 2, until = None, maxTimeBetweenRetries = None, fireRetryExhaustedEvent = None, fireFunctionalEvent = None)

    def withInitialDelay(initialDelay: java.time.Duration) = this.copy(initialDelay = Some(initialDelay))

    def withBackoffFactor(backoffFactor: Double) = this.copy(backoffFactor = backoffFactor)

    def withMaximumRetries(count: Int) = this.copy(until = Some(UntilMaximumRetries(count)))

    def withMaxTimeBetweenRetries(maxTimeBetweenRetries: java.time.Duration) = this.copy(maxTimeBetweenRetries = Some(maxTimeBetweenRetries))

    @Deprecated
    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: String) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent)))

    @Deprecated
    def withFireRetryExhaustedEvent() = this.copy(fireRetryExhaustedEvent = Some(None))

    @Deprecated
    def withFireRetryExhaustedEvent(fireRetryExhaustedEvent: Class[_]) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent.getSimpleName)))

    def withFireEventAndBlock(fireRetryExhaustedEvent: String) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent)))

    def withFireEventAndBlock() = this.copy(fireRetryExhaustedEvent = Some(None))

    def withFireEventAndBlock(fireRetryExhaustedEvent: Class[_]) = this.copy(fireRetryExhaustedEvent = Some(Some(fireRetryExhaustedEvent.getSimpleName)))

    def withFireEventAndResolve(fireRetryExhaustedEvent: String) = this.copy(fireFunctionalEvent = Some(Some(fireRetryExhaustedEvent)))

    def withFireEventAndResolve() = this.copy(fireFunctionalEvent = Some(None))

    def withFireEventAndResolve(fireRetryExhaustedEvent: Class[_]) = this.copy(fireFunctionalEvent = Some(Some(fireRetryExhaustedEvent.getSimpleName)))


    def withDeadline(duration: java.time.Duration) = this.copy(until = Some(UntilDeadline(Duration(duration.toMillis, MILLISECONDS))))

    def build(): RetryWithIncrementalBackoff = {
      require(initialDelay.isDefined, "InitialDelay must be defined")

      var builder = common.InteractionFailureStrategy.RetryWithIncrementalBackoff.builder()
        .withUntil(until)
        .withMaxTimeBetweenRetries(maxTimeBetweenRetries.map(d => Duration(d.toMillis, MILLISECONDS)))
        .withInitialDelay(Duration(initialDelay.get.toMillis, MILLISECONDS))
        .withBackoffFactor(backoffFactor)
      if(fireRetryExhaustedEvent.isDefined)
        builder = builder.withFireEventAndBlock(fireRetryExhaustedEvent.get)
      if(fireFunctionalEvent.isDefined)
        builder = builder.withFireEventAndResolve(fireFunctionalEvent.get)
      builder.build()
    }
  }

  /**
   * @deprecated
   * Please use FireEventAndBlock or FireEventAndResolve, the FireEventAndBlock is exactly as the old FireEvent
   */
  @Deprecated()
  def FireEvent(): common.InteractionFailureStrategy.FireEventAfterFailure = common.InteractionFailureStrategy.FireEventAfterFailure(None)

  /**
   * @deprecated
   * Please use FireEventAndBlock or FireEventAndResolve, the FireEventAndBlock is exactly as the old FireEvent
   */
  @Deprecated()
  def FireEvent(eventClass: Class[_]): common.InteractionFailureStrategy.FireEventAfterFailure =
    FireEvent(eventClass.getSimpleName)

  /**
   * @deprecated
   * Please use FireEventAndBlock or FireEventAndResolve, the FireEventAndBlock is exactly as the old FireEvent
   */
  @Deprecated()
  def FireEvent(eventName: String): common.InteractionFailureStrategy.FireEventAfterFailure =
    common.InteractionFailureStrategy.FireEventAfterFailure(Some(eventName))

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is blocked.
   * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
   * @return
   */
  def FireEventAndBlock(): common.InteractionFailureStrategy.FireEventAndBlock = common.InteractionFailureStrategy.FireEventAndBlock(None)

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is blocked.
   * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
   * @return
   */
  def FireEventAndBlock(eventClass: Class[_]): common.InteractionFailureStrategy.FireEventAndBlock =
    FireEventAndBlock(eventClass.getSimpleName)

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is blocked.
   * Blocked interactions cannot execute again until retryInteraction or resolveInteraction is called on Baker.
   * @return
   */
  def FireEventAndBlock(eventName: String): common.InteractionFailureStrategy.FireEventAndBlock =
    common.InteractionFailureStrategy.FireEventAndBlock(Some(eventName))


  /**
   * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
   * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
   * @return
   */
  def FireEventAndResolve(): common.InteractionFailureStrategy.FireEventAndResolve =
    common.InteractionFailureStrategy.FireEventAndResolve(None)

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
   * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
   * @return
   */
  def FireEventAndResolve(eventClass: Class[_]): common.InteractionFailureStrategy.FireEventAndResolve =
    FireEventAndResolve(eventClass.getSimpleName)

  /**
   * After the interaction fails with an exception an event is thrown and the interaction is not blocked.
   * This means the interaction can be executed again if the preconditions are met but retryInteraction or resolveInteraction cannot be done.
   * @return
   */
  def FireEventAndResolve(eventName: String): common.InteractionFailureStrategy.FireEventAndResolve =
    common.InteractionFailureStrategy.FireEventAndResolve(Some(eventName))

  def BlockInteraction(): BlockInteraction =
    common.InteractionFailureStrategy.BlockInteraction()
}
