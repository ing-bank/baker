package com.ing.baker.runtime.common

import java.util.Base64

import com.ing.baker.il.CompiledRecipe
import com.ing.baker.runtime.serialization.ProtoMap

object Utils {
  def getBase64String(compiledRecipe: CompiledRecipe): String = {
    val protoRecipe: Array[Byte] = ProtoMap.ctxToProto(compiledRecipe).toByteArray
    new String(Base64.getEncoder.encode(protoRecipe))
  }
}