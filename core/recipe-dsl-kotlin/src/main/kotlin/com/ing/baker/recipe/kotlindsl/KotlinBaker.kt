package com.ing.baker.recipe.kotlindsl

import com.squareup.kotlinpoet.FileSpec
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.KModifier
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeSpec
import com.squareup.kotlinpoet.asTypeName
import java.util.concurrent.CompletableFuture
import kotlin.reflect.KFunction
import kotlin.reflect.full.declaredMemberFunctions

class DummyJavaBaker {
    fun foo(banana: String, apple: Int): CompletableFuture<Boolean> = TODO()

    fun bar(kiwi: String, pear: Int): CompletableFuture<List<Int>> = TODO()
}

fun main() {
    val generatedFile = FileSpec.builder("", "SuspendingBaker")
        .addImport("kotlinx.coroutines.future", "await")
        .addType(
            TypeSpec.classBuilder("SuspendingBaker")
                .primaryConstructor(
                    FunSpec.constructorBuilder()
                        .addParameter("baker", DummyJavaBaker::class)
                        .build()
                )
                .addProperty(
                    PropertySpec
                        .builder("baker", DummyJavaBaker::class)
                        .initializer("baker")
                        .addModifiers(KModifier.PRIVATE)
                        .build()
                )
                .addSuspendingFunctions()
                .build()
        ).build()

    generatedFile.writeTo(System.out)
}

private fun TypeSpec.Builder.addSuspendingFunctions(): TypeSpec.Builder {
    DummyJavaBaker::class.declaredMemberFunctions.forEach { memberFunction ->
        addFunction(buildSuspendingFunction(memberFunction))
    }
    return this
}

private fun buildSuspendingFunction(memberFunction: KFunction<*>): FunSpec {
    val builder = FunSpec.builder(memberFunction.name)
        .addModifiers(KModifier.SUSPEND)
        .returns(memberFunction.returnType.arguments.single().type!!.asTypeName())

    memberFunction.parameters.filter { it.name != null }.forEach { parameter ->
        builder.addParameter(parameter.name!!, parameter.type.asTypeName())
    }

    val parameterNames = memberFunction.parameters
        .drop(1)
        .mapNotNull { it.name }
        .joinToString(", ")

    builder.addStatement("return baker.${memberFunction.name}($parameterNames).await()")
    return builder.build()
}
