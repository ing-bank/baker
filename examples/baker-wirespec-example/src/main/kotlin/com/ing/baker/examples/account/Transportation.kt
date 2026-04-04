package com.ing.baker.examples.account

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.kotlin.registerKotlinModule
import community.flock.wirespec.integration.jackson.kotlin.WirespecSerialization
import community.flock.wirespec.kotlin.Wirespec
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import java.lang.reflect.Proxy
import java.net.URI
import java.net.http.HttpClient
import java.net.http.HttpRequest
import java.net.http.HttpResponse
import kotlin.coroutines.Continuation
import kotlin.coroutines.intrinsics.COROUTINE_SUSPENDED

typealias Transportation = suspend (Wirespec.RawRequest) -> Wirespec.RawResponse

@Suppress("UNCHECKED_CAST")
inline fun <reified H : Wirespec.Handler> handle(
    client: Wirespec.Client<*, *>,
    crossinline transport: Transportation,
    serialization: Wirespec.Serialization
): H {
    val edge = client.client(serialization) as Wirespec.ClientEdge<Wirespec.Request<Any>, Wirespec.Response<Any>>
    return Proxy.newProxyInstance(
        H::class.java.classLoader,
        arrayOf(H::class.java)
    ) { proxy, method, args ->
        when (method.name) {
            "toString" -> "TransportHandler(${H::class.simpleName})"
            "hashCode" -> System.identityHashCode(proxy)
            "equals" -> proxy === args?.get(0)
            else -> {
                val request = args[0] as Wirespec.Request<Any>
                val continuation = args[1] as Continuation<Any?>
                CoroutineScope(continuation.context).launch {
                    val result = runCatching {
                        val rawResponse = transport(edge.to(request))
                        edge.from(rawResponse)
                    }
                    continuation.resumeWith(result)
                }
                COROUTINE_SUSPENDED
            }
        }
    } as H
}

fun defaultSerialization(): Wirespec.Serialization =
    WirespecSerialization(ObjectMapper().registerKotlinModule())

fun jvmTransportation(baseUrl: String, client: HttpClient = HttpClient.newHttpClient()): Transportation = { rawRequest ->
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
