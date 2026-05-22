package com.ing.baker.examples.account.openapi

import com.ing.baker.openapi.dsl.api
import com.ing.baker.openapi.dsl.apiRecipe
import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.examples.account.openapi.generated.api.CreateAccount
import com.ing.baker.examples.account.openapi.generated.endpoint.CreateAccount as CreateAccountEndpoint

@OptIn(ExperimentalDsl::class)
object AccountRecipe {
    val apiRecipe = apiRecipe("OpenApiAccount") {
        sensoryEvents { event<CreateAccountCommand>() }

        api(CreateAccount) {
            // CreateAccountCommand is this API's input event — its fields populate
            // the API request. The wirespec CreateAccountRequest DTO never appears
            // in the recipe; only the domain event does. Fields match by name
            // (profileId, accountType, currency); the one mismatch is declared
            // with the symmetric "apiField from eventField" syntax.
            inputFrom<CreateAccountCommand> {
                "userId" from "customerId"
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
