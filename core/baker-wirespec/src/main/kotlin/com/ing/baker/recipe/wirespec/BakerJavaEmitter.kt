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
import community.flock.wirespec.ir.core.Type
import community.flock.wirespec.ir.core.file
import community.flock.wirespec.ir.core.`interface`
import community.flock.wirespec.ir.emit.IrEmitter
import community.flock.wirespec.ir.generator.Generator
import community.flock.wirespec.ir.generator.JavaGenerator

class BakerJavaEmitter(
    private val packageName: PackageName,
) : IrEmitter {

    constructor() : this(PackageName(""))

    override val extension: FileExtension = FileExtension.Java
    override val shared: Shared? = null
    override val generator: Generator = JavaGenerator

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
        val params = collectApplyParams(endpoint)
        val responseClassNames = endpoint.responses.map { "${name}Response${it.status}" }

        return file(interactionName) {
            packageName.takeIf { it.value.isNotEmpty() }
                ?.let { `package`("${it.value}.interaction") }

            import("com.ing.baker.recipe.javadsl", "Interaction")
            import("com.ing.baker.recipe.annotations", "FiresEvent")

            `interface`(interactionName) {
                extends(type("Interaction"))
                `interface`(outcomeName)

                endpoint.responses.forEach { response ->
                    val eventName = "${name}Response${response.status}"
                    val content = response.content
                    if (content != null) {
                        struct(eventName) {
                            implements(type(outcomeName))
                            field("body", content.reference.toIrType())
                        }
                    } else {
                        struct(eventName) {
                            implements(type(outcomeName))
                        }
                    }
                }

                val firesEventArgs = responseClassNames.joinToString(", ") { "$it.class" }
                raw("@FiresEvent(oneOf = {$firesEventArgs})")

                function("apply") {
                    returnType(type(outcomeName))
                    params.forEach { (n, t) -> arg(n, t) }
                }
            }
        }
    }

    override fun emit(type: WsType, module: Module): File = file(type.identifier.value) {}
    override fun emit(enum: Enum, module: Module): File = file(enum.identifier.value) {}
    override fun emit(refined: Refined): File = file(refined.identifier.value) {}
    override fun emit(union: Union): File = file(union.identifier.value) {}
    override fun emit(channel: Channel): File = file(channel.identifier.value) {}

    private fun collectApplyParams(endpoint: Endpoint): List<Pair<String, Type>> = buildList {
        endpoint.path.filterIsInstance<Endpoint.Segment.Param>().forEach {
            add(it.identifier.value to it.reference.toIrType())
        }
        endpoint.queries.forEach { add(it.identifier.value to it.reference.toIrType()) }
        endpoint.headers.forEach { add(it.identifier.value to it.reference.toIrType()) }
        endpoint.requests.forEach { req ->
            val content = req.content ?: return@forEach
            add("body" to content.reference.toIrType())
        }
    }
}
