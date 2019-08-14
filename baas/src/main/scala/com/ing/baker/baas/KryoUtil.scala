package com.ing.baker.baas

import com.ing.baker.runtime.actor.serialization.ExtraKryoSerializersRegistrar
import com.twitter.chill.{KryoPool, ScalaKryoInstantiator}

object KryoUtil {
  val defaultKryoPool: KryoPool = KryoPool.withByteArrayOutputStream(1,
    new ScalaKryoInstantiator()
         .withRegistrar(new ExtraKryoSerializersRegistrar())
  )

  def deserialize[T](bytes: Array[Byte]) =
    defaultKryoPool.fromBytes(bytes).asInstanceOf[T]

  def serialize[T](obj: T): Array[Byte] = defaultKryoPool.toBytesWithClass(obj)
}