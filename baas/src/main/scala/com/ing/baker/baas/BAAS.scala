package com.ing.baker.baas

import akka.actor.ActorSystem
import com.ing.baker.il.CompiledRecipe
import com.ing.baker.recipe.commonserialize.Recipe
import com.ing.baker.recipe.{common, commonserialize}
import com.ing.baker.runtime.core.Baker
import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}

object BAAS{
  val kryoPool = KryoPool.withByteArrayOutputStream(1, new ScalaKryoInstantiator)

  def serializeRecipe(recipe: common.Recipe): Array[Byte] = {
    val commonSerializeRecipe: commonserialize.Recipe = new Recipe(recipe)
    kryoPool.toBytesWithClass(commonSerializeRecipe)
  }

  def deserializeRecipe(serializedRecipe: Array[Byte]): commonserialize.Recipe = {
    kryoPool.fromBytes(serializedRecipe).asInstanceOf[commonserialize.Recipe]
  }

  def serializeCompiledRecipe(compiledRecipe: CompiledRecipe): Array[Byte] = {
    kryoPool.toBytesWithClass(compiledRecipe)
  }

  def deserializeCompiledRecipe(serializedRecipe: Array[Byte]): CompiledRecipe = {
    kryoPool.fromBytes(serializedRecipe).asInstanceOf[CompiledRecipe]
  }
}

class BAAS {
  val baker: Baker = new Baker()(ActorSystem("BAASActorSystem"));
}
