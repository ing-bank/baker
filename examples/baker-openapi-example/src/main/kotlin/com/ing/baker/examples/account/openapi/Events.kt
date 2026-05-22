package com.ing.baker.examples.account.openapi

// Domain-level command. Note `customerId` — the API contract calls it `userId`,
// so the recipe declares an ingredientNameOverride to bridge the two. The other
// fields share names with the API contract and are auto-wired by Baker.
data class CreateAccountCommand(
    val customerId: String,
    val profileId: String,
    val accountType: String,
    val currency: String,
)

data class AccountCreated(val accountId: String, val iban: String)
data class AccountCreationFailed(val reason: String)
