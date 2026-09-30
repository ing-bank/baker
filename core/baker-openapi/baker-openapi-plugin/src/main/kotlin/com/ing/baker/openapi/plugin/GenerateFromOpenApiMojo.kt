package com.ing.baker.openapi.plugin

import arrow.core.nonEmptySetOf
import com.ing.baker.openapi.emitter.BakerOpenApiEmitter
import community.flock.wirespec.compiler.core.emit.EmitShared
import community.flock.wirespec.compiler.core.emit.PackageName
import community.flock.wirespec.emitters.kotlin.KotlinIrEmitter
import community.flock.wirespec.compiler.utils.Logger
import community.flock.wirespec.plugin.ConverterArguments
import community.flock.wirespec.plugin.Format
import community.flock.wirespec.plugin.convert
import community.flock.wirespec.plugin.io.Source
import org.apache.maven.plugin.AbstractMojo
import org.apache.maven.plugin.MojoExecutionException
import org.apache.maven.plugins.annotations.LifecyclePhase
import org.apache.maven.plugins.annotations.Mojo
import org.apache.maven.plugins.annotations.Parameter
import org.apache.maven.project.MavenProject
import java.io.File
import java.nio.file.Files
import java.nio.file.Paths

@Mojo(name = "generate-from-openapi", defaultPhase = LifecyclePhase.GENERATE_SOURCES, threadSafe = true)
class GenerateFromOpenApiMojo : AbstractMojo() {

    @Parameter(required = true)
    private lateinit var input: String

    @Parameter(required = true)
    private lateinit var packageName: String

    @Parameter(defaultValue = "\${project.build.directory}/generated-sources/baker-openapi")
    private lateinit var outputDirectory: String

    @Parameter(defaultValue = "true")
    private var addToSources: Boolean = true

    @Parameter(defaultValue = "\${project}", readonly = true, required = true)
    private lateinit var project: MavenProject

    private val logger: Logger = object : Logger(Level.INFO) {
        override fun debug(string: String) { log.debug(string) }
        override fun info(string: String) { log.info(string) }
        override fun warn(string: String) { log.warn(string) }
        override fun error(string: String) { log.error(string) }
    }

    override fun execute() {
        val inputPath = Paths.get(input)
        if (!Files.exists(inputPath)) {
            throw MojoExecutionException("OpenAPI file not found: $input")
        }
        val json = Files.readString(inputPath)
        val pkg = PackageName(packageName)

        val outDir = File(outputDirectory).apply { mkdirs() }

        val source = Source<Source.Type.JSON>(
            name = community.flock.wirespec.plugin.io.Name(inputPath.fileName.toString().substringBeforeLast('.')),
            content = json,
        )

        val emitters = nonEmptySetOf(
            KotlinIrEmitter(pkg, EmitShared(false)) as community.flock.wirespec.compiler.core.emit.Emitter,
            BakerOpenApiEmitter(pkg) as community.flock.wirespec.compiler.core.emit.Emitter,
        )

        val writer: (arrow.core.NonEmptyList<community.flock.wirespec.compiler.core.emit.Emitted>) -> Unit = { emitted ->
            emitted.forEach { e ->
                val target = File(outDir, e.file)
                target.parentFile.mkdirs()
                target.writeText(e.result)
            }
        }

        val args = ConverterArguments(
            format = Format.OpenAPIV3,
            input = nonEmptySetOf(source),
            emitters = emitters,
            writer = writer,
            error = { msg -> throw MojoExecutionException(msg) },
            packageName = pkg,
            logger = logger,
            shared = false,
            strict = true,
            // We supply KotlinIrEmitter explicitly above; convert() ignores this
            // flag, but ConverterArguments requires it since wirespec 0.18.x.
            ir = true,
        )

        try {
            convert(args)
        } catch (e: Exception) {
            throw MojoExecutionException("OpenAPI conversion failed: ${e.message}", e)
        }

        if (addToSources) {
            project.addCompileSourceRoot(outDir.absolutePath)
            log.info("Added ${outDir.absolutePath} as compile source root")
        }
    }
}
