package com.ing.baker.runtime.common

import java.io.ByteArrayOutputStream
import java.util.zip.GZIPOutputStream

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.serialization.ProtoMap

object Utils {

  def recipeToByteArray(compiledRecipe: CompiledRecipe): Array[Byte] = ProtoMap.ctxToProto(compiledRecipe).toByteArray

  def recipeToGZippedByteArray(compiledRecipe: CompiledRecipe): Array[Byte] = {
    val recipeBytes = recipeToByteArray(compiledRecipe)
    val byteStream = new ByteArrayOutputStream(recipeBytes.length)
    val zipStream = new GZIPOutputStream(byteStream)
    zipStream.write(recipeBytes)
    zipStream.close()
    byteStream.toByteArray
  }

}