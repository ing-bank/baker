package com.ing.baker.examples.account.openapi

data class CreateAccountCommand(
    val userId: String,
    val profileId: String,
    val accountType: String,
    val currency: String,
)

data class AccountCreated(val accountId: String, val iban: String)
data class AccountCreationFailed(val reason: String)
