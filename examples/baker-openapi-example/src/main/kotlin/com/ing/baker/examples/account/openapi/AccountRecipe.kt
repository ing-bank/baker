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
            // The wirespec CreateAccountRequest DTO is never an ingredient — only
            // flat values (path / query / header / flattened body fields) flow
            // through Baker. Each is matched to a recipe ingredient by name:
            //
            //   API field    →   ingredient
            //   profileId    →   profileId    (auto, name matches)
            //   accountType  →   accountType  (auto)
            //   currency     →   currency     (auto)
            //   userId       →   customerId   (override declared below)
            //
            // The descriptor's buildRequest reassembles the DTO inside the
            // generic interaction implementation — out of sight from the recipe.
            ingredientNameOverrides {
                "userId" to "customerId"
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
