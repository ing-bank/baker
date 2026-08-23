type CreateAccountRequest {
  userId: String,
  profileId: String,
  accountType: String,
  currency: String
}

type AccountDto {
  accountId: String,
  userId: String,
  profileId: String,
  iban: String,
  accountType: String,
  currency: String
}

endpoint CreateAccount POST CreateAccountRequest /accounts -> {
  201 -> AccountDto
  400 -> ErrorResponse
}
