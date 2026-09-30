package com.ing.baker.openapi.emitter

import community.flock.wirespec.compiler.core.emit.Emitted
import community.flock.wirespec.compiler.core.emit.FileExtension
import community.flock.wirespec.compiler.core.emit.LanguageEmitter
import community.flock.wirespec.compiler.core.emit.PackageName
import community.flock.wirespec.compiler.core.emit.Shared
import community.flock.wirespec.compiler.core.parse.ast.Channel
import community.flock.wirespec.compiler.core.parse.ast.Definition
import community.flock.wirespec.compiler.core.parse.ast.Endpoint
import community.flock.wirespec.compiler.core.parse.ast.Enum
import community.flock.wirespec.compiler.core.parse.ast.Field
import community.flock.wirespec.compiler.core.parse.ast.Identifier
import community.flock.wirespec.compiler.core.parse.ast.Module
import community.flock.wirespec.compiler.core.parse.ast.Reference
import community.flock.wirespec.compiler.core.parse.ast.Reference.Primitive.Type.Precision
import community.flock.wirespec.compiler.core.parse.ast.Refined
import community.flock.wirespec.compiler.core.parse.ast.Type
import community.flock.wirespec.compiler.core.parse.ast.Union
import community.flock.wirespec.compiler.utils.Logger

class BakerOpenApiEmitter(
    private val packageName: PackageName? = null,
) : LanguageEmitter() {

    private var currentModule: Module? = null

    override val singleLineComment: String = "//"
    override val extension: FileExtension = FileExtension.Kotlin
    override val shared: Shared? = null
    override fun notYetImplemented(): String = ""

    override fun emit(definition: Definition, module: Module, logger: Logger): Emitted {
        currentModule = module
        val base = super.emit(definition, module, logger)
        if (packageName != null && packageName.value.isNotEmpty() && definition is Endpoint) {
            val dir = packageName.value.replace('.', '/') + "/api/"
            return Emitted(dir + base.file, base.result)
        }
        return base
    }

    override fun emit(identifier: Identifier): String = identifier.value

    override fun emit(endpoint: Endpoint): String {
        val name = emit(endpoint.identifier)

        val sb = StringBuilder()
        if (packageName != null && packageName.value.isNotEmpty()) {
            sb.append("package ").append(packageName.value).append(".api\n\n")
            sb.append("import ").append(packageName.value).append(".endpoint.").append(name).append("\n")
            sb.append("import ").append(packageName.value).append(".model.*\n")
        }
        sb.append("import com.ing.baker.openapi.dsl.ApiOperation\n")
        sb.append("import com.ing.baker.openapi.dsl.InputField\n")
        sb.append("import community.flock.wirespec.kotlin.Wirespec\n")
        sb.append("import kotlin.reflect.KClass\n\n")

        // Parameterize ApiOperation by the request body type. Operations without
        // a body use Unit.
        val requestBodyType = bodyTypeName(endpoint) ?: "Unit"
        sb.append("object ").append(name).append(" : ApiOperation<").append(requestBodyType).append("> {\n")
        sb.append("    override val operationName = \"").append(name).append("\"\n\n")

        // Input fields: path + query + headers + flattened body fields.
        // For ::class references we strip nullability — KClass has no nullable variant.
        val inputs = collectInputs(endpoint)
        if (inputs.isEmpty()) {
            sb.append("    override val inputFields: List<InputField> = emptyList()\n\n")
        } else {
            sb.append("    override val inputFields = listOf(\n")
            for (f in inputs) {
                val classRef = if (f[1].endsWith("?")) f[1].substring(0, f[1].length - 1) else f[1]
                sb.append("        InputField(\"").append(f[0]).append("\", ").append(classRef).append("::class),\n")
            }
            sb.append("    )\n\n")
        }

        // Response types
        sb.append("    override val responseTypes: Map<Int, KClass<*>> = mapOf(\n")
        for (resp in endpoint.responses) {
            sb.append("        ").append(resp.status).append(" to ").append(name)
                .append(".Response").append(resp.status).append("::class,\n")
        }
        sb.append("    )\n\n")

        // handlerClass
        sb.append("    override val handlerClass = ").append(name).append(".Handler::class\n\n")

        // buildRequest
        val bodyTypeName = bodyTypeName(endpoint)
        val ctorArgs = ArrayList<String>()
        for (seg in endpoint.path) {
            if (seg is Endpoint.Segment.Param) {
                ctorArgs.add(seg.identifier.value + " = ingredients[\"" + seg.identifier.value + "\"] as " + kotlinType(seg.reference))
            }
        }
        for (q in endpoint.queries) {
            ctorArgs.add(q.identifier.value + " = ingredients[\"" + q.identifier.value + "\"] as " + kotlinType(q.reference))
        }
        for (h in endpoint.headers) {
            ctorArgs.add(h.identifier.value + " = ingredients[\"" + h.identifier.value + "\"] as " + kotlinType(h.reference))
        }
        if (bodyTypeName != null) {
            val bodyType = findType(bodyTypeName)
            val bodyCtor = StringBuilder("$bodyTypeName(")
            if (bodyType != null) {
                val fields = bodyType.shape.value.joinToString(", ") { f ->
                    f.identifier.value + " = ingredients[\"" + f.identifier.value + "\"] as " + kotlinType(f.reference)
                }
                bodyCtor.append(fields)
            }
            bodyCtor.append(")")
            ctorArgs.add(bodyCtor.toString())
        }
        sb.append("    override fun buildRequest(ingredients: Map<String, Any?>): Any =\n")
        if (ctorArgs.isEmpty()) {
            // wirespec emits `object Request` for endpoints with no inputs;
            // reference it as a singleton, not a constructor call.
            sb.append("        ").append(name).append(".Request\n\n")
        } else {
            sb.append("        ").append(name).append(".Request(\n")
            sb.append("            ").append(ctorArgs.joinToString(",\n            ")).append("\n")
            sb.append("        )\n\n")
        }

        // buildRequestFromBody — used by the typed inputFrom<E, R>(mapper) DSL.
        // The user-provided lambda returns the body DTO; this wraps it in the
        // Endpoint.Request envelope. Body-only operations have a trivial wrapper;
        // operations with path/query/header params reject the typed flow in v1.
        val bodyOnly = bodyTypeName != null &&
            endpoint.queries.isEmpty() &&
            endpoint.headers.isEmpty() &&
            endpoint.path.none { it is Endpoint.Segment.Param }
        sb.append("    override fun buildRequestFromBody(body: ").append(requestBodyType).append("): Any =\n")
        if (bodyOnly) {
            sb.append("        ").append(name).append(".Request(body)\n\n")
        } else if (bodyTypeName == null) {
            sb.append("        error(\"Operation ").append(name).append(" has no request body; inputFrom is not applicable.\")\n\n")
        } else {
            sb.append("        error(\"inputFrom { ... } is not supported for operations with path/query/header params; use ingredientNameOverrides with the flat flow instead.\")\n\n")
        }

        // invoke
        val handlerMethod = name.replaceFirstChar { it.lowercaseChar() }
        sb.append("    override suspend fun invoke(handler: Wirespec.Handler, request: Any): Wirespec.Response<*> =\n")
        sb.append("        (handler as ").append(name).append(".Handler).").append(handlerMethod)
            .append("(request as ").append(name).append(".Request)\n\n")

        // buildHandler — wraps the operation's wirespec ClientEdge in a Handler that
        // routes through the supplied transport. Lets callers register no per-operation
        // factories — only (transport, serialization) at startup.
        sb.append("    override fun buildHandler(\n")
        sb.append("        transport: suspend (Wirespec.RawRequest) -> Wirespec.RawResponse,\n")
        sb.append("        serialization: Wirespec.Serialization,\n")
        sb.append("    ): Wirespec.Handler {\n")
        sb.append("        val edge = ").append(name).append(".Handler.client(serialization)\n")
        sb.append("        return object : ").append(name).append(".Handler {\n")
        sb.append("            override suspend fun ").append(handlerMethod)
            .append("(request: ").append(name).append(".Request): ")
            .append(name).append(".Response<*> =\n")
        sb.append("                edge.from(transport(edge.to(request)))\n")
        sb.append("        }\n")
        sb.append("    }\n")
        sb.append("}\n")

        return sb.toString()
    }

    override fun emit(type: Type, module: Module): String = notYetImplemented()
    override fun Type.Shape.emit(): String = notYetImplemented()
    override fun Field.emit(): String = notYetImplemented()
    override fun Reference.emit(): String = kotlinType(this)
    override fun Reference.Primitive.Type.Constraint.emit(): String = notYetImplemented()
    override fun emit(enum: Enum, module: Module): String = notYetImplemented()
    override fun emit(union: Union): String = notYetImplemented()
    override fun emit(refined: Refined): String = notYetImplemented()
    override fun Refined.emitValidator(): String = notYetImplemented()
    override fun emit(channel: Channel): String = notYetImplemented()

    private fun collectInputs(endpoint: Endpoint): List<Array<String>> {
        val out = ArrayList<Array<String>>()
        for (seg in endpoint.path) {
            if (seg is Endpoint.Segment.Param) {
                out.add(arrayOf(seg.identifier.value, kotlinType(seg.reference)))
            }
        }
        for (q in endpoint.queries) {
            out.add(arrayOf(q.identifier.value, kotlinType(q.reference)))
        }
        for (h in endpoint.headers) {
            out.add(arrayOf(h.identifier.value, kotlinType(h.reference)))
        }
        for (req in endpoint.requests) {
            val ref = req.content?.reference
            if (ref is Reference.Custom) {
                val bodyType = findType(ref.value)
                if (bodyType != null) {
                    for (f in bodyType.shape.value) {
                        out.add(arrayOf(f.identifier.value, kotlinType(f.reference)))
                    }
                }
            }
        }
        return out
    }

    private fun bodyTypeName(endpoint: Endpoint): String? {
        for (req in endpoint.requests) {
            val ref = req.content?.reference
            if (ref is Reference.Custom) {
                return ref.value
            }
        }
        return null
    }

    private fun findType(name: String): Type? {
        val module = currentModule ?: return null
        for (stmt in module.statements) {
            if (stmt is Type && stmt.identifier.value == name) return stmt
        }
        return null
    }

    private fun kotlinType(ref: Reference): String {
        val base = when (ref) {
            is Reference.Primitive -> when (val type = ref.type) {
                is Reference.Primitive.Type.String -> "String"
                is Reference.Primitive.Type.Integer -> when (type.precision) {
                    Precision.P32 -> "Int"
                    Precision.P64 -> "Long"
                }
                is Reference.Primitive.Type.Number -> when (type.precision) {
                    Precision.P32 -> "Float"
                    Precision.P64 -> "Double"
                }
                is Reference.Primitive.Type.Boolean -> "Boolean"
                is Reference.Primitive.Type.Bytes -> "ByteArray"
            }
            is Reference.Custom -> ref.value
            is Reference.Iterable -> "List<" + kotlinType(ref.reference) + ">"
            is Reference.Dict -> "Map<String, " + kotlinType(ref.reference) + ">"
            is Reference.Unit -> "Unit"
            is Reference.Any -> "Any"
        }
        return if (ref.isNullable) "$base?" else base
    }
}
