package com.ing.baker.examples.account

data class CreateCurrentAccountEvent(
    val firstName: String,
    val lastName: String,
    val email: String,
    val dateOfBirth: String,
    val address: String,
    val phoneNumber: String,
    val accountType: String,
    val currency: String
)
