type CreateUserRequest {
  firstName: String,
  lastName: String,
  email: String,
  dateOfBirth: String
}

type UserDto {
  id: String,
  firstName: String,
  lastName: String,
  email: String,
  dateOfBirth: String
}

type ErrorResponse {
  code: String,
  message: String
}

endpoint CreateUser POST CreateUserRequest /users -> {
  201 -> UserDto
  400 -> ErrorResponse
}
