package com.ing.baker.runtime.core.events;

public enum RejectReason {
    
    NoSuchProcess,
    ProcessDeleted,
    AlreadReceived,
    ReceivePeriodExpired,
    FiringLimitMet,
    InvalidEvent
}
