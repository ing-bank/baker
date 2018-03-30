package com.ing.baker.runtime.core;

/**
 *  Describes how baker processed an event.
 */
public enum SensoryEventStatus {
    
    /**
     * The event was received.
     */
    Received,

    /**
     * The event was received and all subsequent interactions processed.
     */
    Completed,

    /**
     *  The event was not accepted because the firing limit
     *  of that event was met.
     */
    FiringLimitMet,

    /**
     * The event was not accepted because the receive period
     * in which events can be received for the recipe was passed.
     */
    ReceivePeriodExpired,

    /**
     * The event was not accepted because it was already
     * received before.
     */
    AlreadyReceived,

    /**
     * The event was not accepted because the process
     * was deleted.
     */
    ProcessDeleted
}
