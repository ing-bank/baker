package com.ing.baker.runtime.actor.serialization

import akka.actor.ExtendedActorSystem
import akka.serialization.SerializerWithStringManifest

class DummyLocalSerializer(system: ExtendedActorSystem) extends SerializerWithStringManifest {

  override def identifier: Int = 103

  override def manifest(o: AnyRef): String = throw new IllegalStateException(s"The DummyLocalSerializer should never be called, manifest called for: ${o.getClass.getName}")

  override def toBinary(o: AnyRef): Array[Byte] = throw new IllegalStateException(s"The DummyLocalSerializer should never used, toBinary called for: ${o.getClass.getName}")

  override def fromBinary(bytes: Array[Byte], manifest: String): AnyRef = throw new IllegalStateException(s"This DummyLocalSerializer should never be called, fromBinary called for: $manifest")
}
