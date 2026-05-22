package com.ing.baker.examples.account.openapi

import com.ing.baker.openapi.dsl.api
import com.ing.baker.openapi.dsl.apiRecipe
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.examples.account.openapi.generated.api.CreateAccount
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint
import com.ing.baker.examples.account.openapi.generated.model.CreateAccountRequest

@OptIn(ExperimentalDsl::class)
object AccountRecipe {
    val apiRecipe = apiRecipe("OpenApiAccount") {
        sensoryEvents { event<CreateAccountCommand>() }

        api(CreateAccount) {
            // The DSL is symmetric on both sides — the wirespec request/response
            // DTOs appear inside the mapping lambdas only, never as ingredients.
            //
            //   Input :  inputFrom<EventType, RequestType>(...)
            //   Output:  on<ResponseType, EventType>(N, ...)
            inputFrom<CreateAccountCommand, CreateAccountRequest> { cmd ->
                CreateAccountRequest(
                    userId = cmd.customerId,
                    profileId = cmd.profileId,
                    accountType = cmd.accountType,
                    currency = cmd.currency,
                )
            }

            on<CreateAccountEndpoint.Response201, AccountCreated>(201) { resp ->
                AccountCreated(accountId = resp.body.accountId, iban = resp.body.iban)
            }
            on<CreateAccountEndpoint.Response400, AccountCreationFailed>(400) { resp ->
                AccountCreationFailed(reason = resp.body.message)
            }
        }
    }
}
