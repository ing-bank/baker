package com.ing.baker.runtime.actor.serialization

import javax.crypto.BadPaddingException

import akka.actor.ActorSystem
import com.ing.baker.runtime.actor.serialization.Encryption._
import org.scalatest.{FunSuite, Matchers}

class ObjectSerializerSpec extends FunSuite with Matchers {

  test("serialize/deserialize data with encryption") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new ObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new ObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))

    val serializedData = serializer1.serializeObject(someEvent)

    serializer2.deserializeObject(serializedData) shouldBe someEvent
  }

  test("cannot deserialize data back if another encryption secret is used") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new ObjectSerializer(actorSystem, new AESEncryption("0123456789123456"))
    val serializer2 = new ObjectSerializer(actorSystem, new AESEncryption("0123456789123459"))

    val serializedData = serializer1.serializeObject(someEvent)

    // fails during decryption and throws this exception
    intercept[BadPaddingException] {
      serializer2.deserializeObject(serializedData)
    }
  }

  test("serialize/deserialize data without encryption") {
    val someEvent = "some event"
    val actorSystem = ActorSystem()
    val serializer1 = new ObjectSerializer(actorSystem, NoEncryption)
    val serializer2 = new ObjectSerializer(actorSystem, NoEncryption)

    val serializedData = serializer1.serializeObject(someEvent)

    serializer2.deserializeObject(serializedData) shouldBe someEvent
  }

}
