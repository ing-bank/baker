package com.ing.baker.runtime.core.events;

public enum RejectReason {
    NoSuchProcess,
    ProcessDeleted,
    AlreadyReceived,
    ReceivePeriodExpired,
    FiringLimitMet,
    InvalidEvent
}
