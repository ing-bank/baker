package com.ing.baker.runtime.core;

/**
 * A status object indicating how baker reacted to an event it received.
 */
public enum SensoryEventStatus {
    /**
     * The event was received and accepted.
     */
    Received,
    /**
     * The event was received and all resulting actions were executed.
     */
    Completed,
    /**
     * The firing limit, the number of times this event may fire, was met.
     */
    FiringLimitMet,
    /**
     * The receive period in which events may be accepted was expired for this process instance.
     */
    ReceivePeriodExpired,
    /**
     * An event with the same correlation id was already received.
     */
    AlreadyReceived,
    /**
     * The process instance was deleted.
     */
    ProcessDeleted
}
