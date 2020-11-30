package com.ing.baker.runtime.common

import java.util.Base64

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.serialization.ProtoMap
import java.io.ByteArrayOutputStream
import java.util.zip.GZIPOutputStream

object Utils {

  def recipeToByteArray(compiledRecipe: CompiledRecipe): Array[Byte] = ProtoMap.ctxToProto(compiledRecipe).toByteArray

  def getBase64String(compiledRecipe: CompiledRecipe): String = new String(Base64.getEncoder.encode(recipeToByteArray(compiledRecipe)))

  def recipeToGZippedByteArray(compiledRecipe: CompiledRecipe): Array[Byte] = {
    val recipeBytes = recipeToByteArray(compiledRecipe)
    val byteStream = new ByteArrayOutputStream(recipeBytes.length)
    val zipStream = new GZIPOutputStream(byteStream)
    zipStream.write(recipeBytes)
    zipStream.close()
    byteStream.toByteArray
  }

}