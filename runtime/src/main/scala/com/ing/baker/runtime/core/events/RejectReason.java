package com.ing.baker.runtime.core.events;

public enum RejectReason {
    /**
     * The process for which the event was received does not exist
     */
    NoSuchProcess,
    /**
     * The process for which the event was received was deleted
     */
    ProcessDeleted,
    /**
     * The event was already received before
     */
    AlreadyReceived,
    /**
     * The time for which events may received for this process was expired
     */
    ReceivePeriodExpired,
    /**
     * The limit (number of times) that this event may be processed was met
     */
    FiringLimitMet,
    /**
     * The event was not valid
     *
     * Reasons could be:
     * - an event with an unknown name was given
     * - null values for ingredients were found
     */
    InvalidEvent
}
