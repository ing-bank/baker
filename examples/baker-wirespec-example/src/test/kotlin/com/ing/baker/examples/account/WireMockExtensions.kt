package com.ing.baker.examples.account

import com.github.tomakehurst.wiremock.WireMockServer
import com.github.tomakehurst.wiremock.client.WireMock.*
import community.flock.wirespec.kotlin.Wirespec
import kotlin.reflect.full.companionObject
import kotlin.reflect.full.companionObjectInstance
import kotlin.reflect.full.declaredMemberProperties
import kotlin.reflect.full.memberFunctions

fun WireMockServer.stubFor(response: Wirespec.Response<*>) {
    val serialization: Wirespec.Serialization = defaultSerialization()
    val responseClass = response::class.java
    val endpointClass = responseClass.enclosingClass
        ?: error("Response class ${responseClass.name} has no enclosing class")

    val endpointInstance = endpointClass.kotlin.objectInstance
        ?: error("Enclosing class ${endpointClass.name} is not a Kotlin object")

    // Serialize the response via the endpoint's toResponse
    val toResponse = endpointClass.kotlin.memberFunctions
        .find { it.name == "toResponse" }
        ?: error("No toResponse method found on ${endpointClass.name}")
    val rawResponse = toResponse.call(endpointInstance, serialization, response) as Wirespec.RawResponse

    // Get path and method from the Handler companion
    val handlerClass = endpointClass.declaredClasses
        .find { it.simpleName == "Handler" }
        ?: error("No Handler interface found in ${endpointClass.name}")
    val handlerCompanion = handlerClass.kotlin.companionObjectInstance
        ?: error("No companion object found on Handler")
    val pathTemplate = handlerClass.kotlin.companionObject!!.declaredMemberProperties
        .find { it.name == "pathTemplate" }!!
        .call(handlerCompanion) as String
    val method = handlerClass.kotlin.companionObject!!.declaredMemberProperties
        .find { it.name == "method" }!!
        .call(handlerCompanion) as String

    val requestPattern = when (method) {
        "GET" -> get(urlEqualTo(pathTemplate))
        "POST" -> post(urlEqualTo(pathTemplate))
        "PUT" -> put(urlEqualTo(pathTemplate))
        "DELETE" -> delete(urlEqualTo(pathTemplate))
        "PATCH" -> patch(urlEqualTo(pathTemplate))
        else -> error("Unsupported HTTP method: $method")
    }

    stubFor(
        requestPattern.willReturn(
            aResponse()
                .withStatus(rawResponse.statusCode)
                .withHeader("Content-Type", "application/json")
                .withBody(rawResponse.body)
        )
    )
}
