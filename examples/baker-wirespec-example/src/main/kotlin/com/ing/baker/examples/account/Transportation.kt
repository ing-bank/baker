package com.ing.baker.examples.account

import community.flock.wirespec.kotlin.Wirespec
import java.net.URI
import java.net.http.HttpClient
import java.net.http.HttpRequest
import java.net.http.HttpResponse

typealias Transportation = suspend (Wirespec.RawRequest) -> Wirespec.RawResponse

fun javaHttpTransportation(baseUrl: String, client: HttpClient = HttpClient.newHttpClient()): Transportation = { rawRequest ->
    val path = rawRequest.path.joinToString("/")
    val queryString = rawRequest.queries
        .flatMap { (key, values) -> values.map { "$key=$it" } }
        .joinToString("&")
        .let { if (it.isNotEmpty()) "?$it" else "" }

    val uri = URI.create("$baseUrl/$path$queryString")

    val bodyPublisher = rawRequest.body
        ?.let { HttpRequest.BodyPublishers.ofByteArray(it) }
        ?: HttpRequest.BodyPublishers.noBody()

    val builder = HttpRequest.newBuilder()
        .uri(uri)
        .method(rawRequest.method, bodyPublisher)

    rawRequest.headers.forEach { (name, values) ->
        values.forEach { value -> builder.header(name, value) }
    }

    if (rawRequest.body != null) {
        builder.header("Content-Type", "application/json")
    }

    val response = client.send(builder.build(), HttpResponse.BodyHandlers.ofByteArray())

    val responseHeaders = response.headers().map()
        .mapValues { (_, values) -> values.toList() }

    Wirespec.RawResponse(
        statusCode = response.statusCode(),
        headers = responseHeaders,
        body = response.body()?.takeIf { it.isNotEmpty() }
    )
}
