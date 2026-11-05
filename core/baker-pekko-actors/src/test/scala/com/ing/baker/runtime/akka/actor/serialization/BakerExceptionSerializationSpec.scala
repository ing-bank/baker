package com.ing.baker.runtime.akka.actor.serialization

import org.apache.pekko.actor.{ActorSystem, Status}
import org.apache.pekko.serialization.{SerializationExtension, Serializers}
import org.apache.pekko.testkit.TestKit
import com.ing.baker.runtime.common.BakerException.IllegalInteractionStateException
import com.typesafe.config.ConfigFactory
import org.scalatest.funsuite.AnyFunSuiteLike
import org.scalatest.matchers.should.Matchers

object BakerExceptionSerializationSpec {
  // Java serialization is disabled in the Baker runtime (see baker.conf), which is what makes pekko replace
  // throwables without a configured serializer by a ThrowableNotSerializableException.
  val config = ConfigFactory
    .parseString("pekko.actor.allow-java-serialization = off")
    .withFallback(ConfigFactory.load())
}

class BakerExceptionSerializationSpec
  extends TestKit(ActorSystem("BakerExceptionSerializationSpec", BakerExceptionSerializationSpec.config))
    with AnyFunSuiteLike
    with Matchers {

  test("a BakerException inside a Status.Failure survives remote serialization") {
    val serialization = SerializationExtension(system)
    val message = Status.Failure(IllegalInteractionStateException("Interaction is not blocked"))

    val serializer = serialization.findSerializerFor(message)
    val bytes = serialization.serialize(message).get
    val manifest = Serializers.manifestFor(serializer, message)

    val deserialized = serialization
      .deserialize(bytes, serializer.identifier, manifest)
      .get
      .asInstanceOf[Status.Failure]

    deserialized.cause shouldBe a[IllegalInteractionStateException]
    deserialized.cause.getMessage shouldBe "Interaction is not blocked"
  }
}
