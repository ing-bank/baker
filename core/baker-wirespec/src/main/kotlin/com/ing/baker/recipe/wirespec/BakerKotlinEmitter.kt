package com.ing.baker.recipe.wirespec

import arrow.core.NonEmptyList
import arrow.core.toNonEmptyListOrNull
import community.flock.wirespec.compiler.core.emit.Emitted
import community.flock.wirespec.compiler.core.emit.FileExtension
import community.flock.wirespec.compiler.core.emit.PackageName
import community.flock.wirespec.compiler.core.emit.Shared
import community.flock.wirespec.compiler.core.parse.ast.AST
import community.flock.wirespec.compiler.core.parse.ast.Channel
import community.flock.wirespec.compiler.core.parse.ast.Endpoint
import community.flock.wirespec.compiler.core.parse.ast.Enum
import community.flock.wirespec.compiler.core.parse.ast.Module
import community.flock.wirespec.compiler.core.parse.ast.Reference
import community.flock.wirespec.compiler.core.parse.ast.Refined
import community.flock.wirespec.compiler.core.parse.ast.Type as WsType
import community.flock.wirespec.compiler.core.parse.ast.Union
import community.flock.wirespec.compiler.utils.Logger
import community.flock.wirespec.ir.core.File
import community.flock.wirespec.ir.core.Name
import community.flock.wirespec.ir.core.Precision
import community.flock.wirespec.ir.core.RawExpression
import community.flock.wirespec.ir.core.Type
import community.flock.wirespec.ir.core.VariableReference
import community.flock.wirespec.ir.core.file
import community.flock.wirespec.ir.core.`interface`
import community.flock.wirespec.ir.emit.IrEmitter
import community.flock.wirespec.ir.generator.Generator
import community.flock.wirespec.ir.generator.KotlinGenerator

class BakerKotlinEmitter(
    private val packageName: PackageName,
) : IrEmitter {

    constructor() : this(PackageName(""))

    override val extension: FileExtension = FileExtension.Kotlin
    override val shared: Shared? = null
    override val generator: Generator = KotlinGenerator

    private var currentModule: Module? = null

    internal fun setModule(module: Module) {
        currentModule = module
    }

    override fun emit(ast: AST, logger: Logger): NonEmptyList<Emitted> {
        val files = ast.modules.toList().flatMap { module ->
            currentModule = module
            module.statements.filterIsInstance<Endpoint>().map { emit(it) }
        }
        val nel = files.toNonEmptyListOrNull()
            ?: return NonEmptyList(Emitted("empty." + extension.value, ""), emptyList())
        return nel.map { f -> Emitted(buildFileName(f), generator.generate(f)) }
    }

    private fun buildFileName(file: File): String {
        val dir = packageName.takeIf { it.value.isNotEmpty() }
            ?.let { it.value.replace('.', '/') + "/interaction/" }
            ?: ""
        return dir + file.name.value() + "." + extension.value
    }

    override fun emit(endpoint: Endpoint): File {
        val name = endpoint.identifier.value
        val interactionName = "${name}Interaction"
        val outcomeName = "${name}Outcome"
        val handlerMethod = name.replaceFirstChar { it.lowercaseChar() }

        val params = collectApplyParams(endpoint)
        val bodyTypeName = requestBodyCustomTypeName(endpoint)
        val bodyType = bodyTypeName?.let { findTypeInModule(it) }
        val customTypes = collectCustomTypeNames(endpoint)

        return file(interactionName) {
            packageName.takeIf { it.value.isNotEmpty() }
                ?.let { `package`("${it.value}.interaction") }

            import("com.ing.baker.recipe.javadsl", "Interaction")
            import("kotlinx.coroutines", "runBlocking")
            packageName.takeIf { it.value.isNotEmpty() }?.let { pkg ->
                import("${pkg.value}.endpoint", name)
                customTypes.forEach { t -> import("${pkg.value}.model", t) }
            }

            `interface`(interactionName) {
                extends(type("Interaction"))
                `interface`(outcomeName, isSealed = true)

                endpoint.responses.forEach { response ->
                    val eventName = "${name}Response${response.status}"
                    val content = response.content
                    when {
                        content == null -> struct(eventName) {
                            implements(type(outcomeName))
                            constructo {}
                        }
                        content.reference is Reference.Custom &&
                            findTypeInModule((content.reference as Reference.Custom).value) != null -> {
                            val respType = findTypeInModule((content.reference as Reference.Custom).value)!!
                            struct(eventName) {
                                implements(type(outcomeName))
                                respType.shape.value.forEach {
                                    field(it.identifier.value, it.reference.toIrType())
                                }
                            }
                        }
                        else -> struct(eventName) {
                            implements(type(outcomeName))
                            field("body", content.reference.toIrType())
                        }
                    }
                }

                function("apply") {
                    returnType(type(outcomeName))
                    params.forEach { (n, t) -> arg(n, t) }
                }
            }

            struct("${interactionName}Impl") {
                implements(type(interactionName))
                field("client", type("$name.Handler"))

                function("apply", isOverride = true) {
                    returnType(type("$interactionName.$outcomeName"))
                    params.forEach { (n, t) -> arg(n, t) }

                    val requestArgNames = buildList {
                        if (bodyType != null) {
                            val bodyArgs = bodyType.shape.value.joinToString(", ") { f ->
                                val n = f.identifier.value
                                "$n = $n"
                            }
                            assign("body", RawExpression("$bodyTypeName($bodyArgs)"))
                        }
                        endpoint.path.filterIsInstance<Endpoint.Segment.Param>()
                            .forEach { add(it.identifier.value) }
                        endpoint.queries.forEach { add(it.identifier.value) }
                        endpoint.headers.forEach { add(it.identifier.value) }
                        endpoint.requests.forEach { req -> if (req.content != null) add("body") }
                    }
                    assign(
                        "request",
                        RawExpression("$name.Request(${requestArgNames.joinToString(", ")})"),
                    )
                    assign(
                        "response",
                        RawExpression("runBlocking { client.$handlerMethod(request) }"),
                    )

                    switch(VariableReference(Name.of("response"))) {
                        endpoint.responses.forEach { response ->
                            val eventName = "${name}Response${response.status}"
                            val qualifiedEventName = "$interactionName.$eventName"
                            case(type("$name.Response${response.status}")) {
                                val content = response.content
                                when {
                                    content == null -> returns(RawExpression(qualifiedEventName))
                                    content.reference is Reference.Custom &&
                                        findTypeInModule((content.reference as Reference.Custom).value) != null -> {
                                        val respType = findTypeInModule((content.reference as Reference.Custom).value)!!
                                        val fields = respType.shape.value.joinToString(", ") { f ->
                                            val n = f.identifier.value
                                            "$n = response.body.$n"
                                        }
                                        returns(RawExpression("$qualifiedEventName($fields)"))
                                    }
                                    else -> returns(RawExpression("$qualifiedEventName(response.body)"))
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    override fun emit(type: WsType, module: Module): File = file(type.identifier.value) {}
    override fun emit(enum: Enum, module: Module): File = file(enum.identifier.value) {}
    override fun emit(refined: Refined): File = file(refined.identifier.value) {}
    override fun emit(union: Union): File = file(union.identifier.value) {}
    override fun emit(channel: Channel): File = file(channel.identifier.value) {}

    private fun findTypeInModule(typeName: String): WsType? = currentModule
        ?.statements
        ?.firstOrNull { it is WsType && it.identifier.value == typeName } as? WsType

    private fun collectApplyParams(endpoint: Endpoint): List<Pair<String, Type>> = buildList {
        endpoint.path.filterIsInstance<Endpoint.Segment.Param>().forEach {
            add(it.identifier.value to it.reference.toIrType())
        }
        endpoint.queries.forEach { add(it.identifier.value to it.reference.toIrType()) }
        endpoint.headers.forEach { add(it.identifier.value to it.reference.toIrType()) }
        endpoint.requests.forEach { req ->
            val content = req.content ?: return@forEach
            val ref = content.reference
            if (ref is Reference.Custom) {
                val bodyType = findTypeInModule(ref.value)
                if (bodyType != null) {
                    bodyType.shape.value.forEach {
                        add(it.identifier.value to it.reference.toIrType())
                    }
                    return@forEach
                }
            }
            add("body" to ref.toIrType())
        }
    }

    private fun requestBodyCustomTypeName(endpoint: Endpoint): String? =
        endpoint.requests.firstNotNullOfOrNull { req ->
            (req.content?.reference as? Reference.Custom)?.value
        }

    private fun collectCustomTypeNames(endpoint: Endpoint): Set<String> = buildSet {
        endpoint.requests.forEach { req ->
            req.content?.reference?.let { ref ->
                addCustomTypes(ref, this)
                if (ref is Reference.Custom) {
                    findTypeInModule(ref.value)?.shape?.value?.forEach {
                        addCustomTypes(it.reference, this)
                    }
                }
            }
        }
        endpoint.responses.forEach { res ->
            res.content?.reference?.let { ref ->
                addCustomTypes(ref, this)
                if (ref is Reference.Custom) {
                    findTypeInModule(ref.value)?.shape?.value?.forEach {
                        addCustomTypes(it.reference, this)
                    }
                }
            }
        }
    }

    private fun addCustomTypes(ref: Reference, acc: MutableSet<String>) {
        when (ref) {
            is Reference.Custom -> acc.add(ref.value)
            is Reference.Iterable -> addCustomTypes(ref.reference, acc)
            is Reference.Dict -> addCustomTypes(ref.reference, acc)
            else -> Unit
        }
    }
}

internal fun Reference.toIrType(): Type {
    val base: Type = when (this) {
        is Reference.Primitive -> when (val t = type) {
            is Reference.Primitive.Type.String -> Type.String
            is Reference.Primitive.Type.Integer -> when (t.precision) {
                Reference.Primitive.Type.Precision.P32 -> Type.Integer(Precision.P32)
                Reference.Primitive.Type.Precision.P64 -> Type.Integer(Precision.P64)
            }
            is Reference.Primitive.Type.Number -> when (t.precision) {
                Reference.Primitive.Type.Precision.P32 -> Type.Number(Precision.P32)
                Reference.Primitive.Type.Precision.P64 -> Type.Number(Precision.P64)
            }
            Reference.Primitive.Type.Boolean -> Type.Boolean
            Reference.Primitive.Type.Bytes -> Type.Bytes
        }
        is Reference.Custom -> Type.Custom(value)
        is Reference.Iterable -> Type.Array(reference.toIrType())
        is Reference.Dict -> Type.Dict(Type.String, reference.toIrType())
        is Reference.Unit -> Type.Unit
        is Reference.Any -> Type.Any
    }
    return if (isNullable) Type.Nullable(base) else base
}
