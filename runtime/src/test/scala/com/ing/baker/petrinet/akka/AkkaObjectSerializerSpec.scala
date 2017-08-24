package com.ing.baker.petrinet.akka

import javax.crypto.BadPaddingException

import akka.actor.ActorSystem
import com.ing.baker.serialization.Encryption.{AESEncryption, NoEncryption}
import org.scalatest.{FunSuite, Matchers}

class AkkaObjectSerializerSpec extends FunSuite with Matchers {

  test("serialize/deserialize data with encryption") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new AkkaObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new AkkaObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))

    val serializedData = serializer1.serializeObject(someEvent)

    serializer2.deserializeObject(serializedData) shouldBe someEvent
  }

  test("cannot deserialize data back if another encryption secret is used") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new AkkaObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new AkkaObjectSerializer(actorSystem, new AESEncryption("0123456789123459"))

    val serializedData = serializer1.serializeObject(someEvent)

    // fails during decryption and throws this exception
    intercept[BadPaddingException] {
      serializer2.deserializeObject(serializedData)
    }
  }

  test("serialize/deserialize data without encryption") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new AkkaObjectSerializer(actorSystem, NoEncryption)
    val serializer2 = new AkkaObjectSerializer(actorSystem, NoEncryption)

    val serializedData = serializer1.serializeObject(someEvent)

    serializer2.deserializeObject(serializedData) shouldBe someEvent
  }

}
