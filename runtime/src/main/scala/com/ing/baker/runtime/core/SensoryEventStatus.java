package com.ing.baker.runtime.core;

public enum SensoryEventStatus {
    Received,
    EventNotFired,
    EventFired,
    Completed,

    FiringLimitMet,
    ReceivePeriodExpired
}
