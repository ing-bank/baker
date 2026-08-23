package com.ing.baker.examples.account

import community.flock.wirespec.kotlin.Wirespec
import com.ing.baker.examples.account.generated.endpoint.CreateUser
import com.ing.baker.examples.account.generated.endpoint.CreateProfile
import com.ing.baker.examples.account.generated.endpoint.CreateAccount


fun createUserHandler(transport: Transportation, serialization: Wirespec.Serialization): CreateUser.Handler {
    val edge = CreateUser.Handler.client(serialization)
    return object : CreateUser.Handler {
        override suspend fun createUser(request: CreateUser.Request): CreateUser.Response<*> {
            val rawResponse = transport(edge.to(request))
            return edge.from(rawResponse)
        }
    }
}

fun createProfileHandler(transport: Transportation, serialization: Wirespec.Serialization): CreateProfile.Handler {
    val edge = CreateProfile.Handler.client(serialization)
    return object : CreateProfile.Handler {
        override suspend fun createProfile(request: CreateProfile.Request): CreateProfile.Response<*> {
            val rawResponse = transport(edge.to(request))
            return edge.from(rawResponse)
        }
    }
}

fun createAccountHandler(transport: Transportation, serialization: Wirespec.Serialization): CreateAccount.Handler {
    val edge = CreateAccount.Handler.client(serialization)
    return object : CreateAccount.Handler {
        override suspend fun createAccount(request: CreateAccount.Request): CreateAccount.Response<*> {
            val rawResponse = transport(edge.to(request))
            return edge.from(rawResponse)
        }
    }
}
