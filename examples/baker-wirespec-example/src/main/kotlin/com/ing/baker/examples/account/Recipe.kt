package com.ing.baker.examples.account

import com.ing.baker.recipe.kotlindsl.ExperimentalDsl
import com.ing.baker.recipe.kotlindsl.recipe
import com.ing.baker.examples.account.generated.*

@ExperimentalDsl
object Recipe {
    val recipe = recipe("CreateCurrentAccount") {
        sensoryEvents {
            event<CreateCurrentAccountEvent>()
        }

        // Step 1: Create user — picks up firstName, lastName, email, dateOfBirth from sensory event
        interaction<CreateUserInteraction> {
            maximumInteractionCount = 1
        }

        // Step 2: Create profile — userId comes from CreateUser's "id" ingredient
        interaction<CreateProfileInteraction> {
            maximumInteractionCount = 1
            ingredientNameOverrides {
                "userId" to "id"
            }
            requiredEvents {
                event<CreateUserInteraction.CreateUserResponse201>()
            }
        }

        // Step 3: Create account — userId from "id", profileId from CreateProfile response
        interaction<CreateAccountInteraction> {
            maximumInteractionCount = 1
            ingredientNameOverrides {
                "userId" to "id"
            }
            requiredEvents {
                event<CreateUserInteraction.CreateUserResponse201>()
                event<CreateProfileInteraction.CreateProfileResponse201>()
            }
        }

        // Fires when all three APIs have responded successfully
        checkpointEvent("Finish") {
            requiredEvents {
                event<CreateUserInteraction.CreateUserResponse201>()
                event<CreateProfileInteraction.CreateProfileResponse201>()
                event<CreateAccountInteraction.CreateAccountResponse201>()
            }
        }
    }
}
