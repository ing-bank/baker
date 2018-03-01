package com.ing.baker.runtime.actor.serialization

import akka.actor.ActorSystem
import akka.serialization.SerializationExtension
import akka.testkit.TestKit
import com.ing.baker.types.{PrimitiveValue, Value}
import com.ing.baker.runtime.core.{ProcessState, RuntimeEvent}
import org.scalacheck.Prop.forAll
import org.scalacheck.{Gen, Test}
import org.scalatest.FunSuiteLike
import org.scalatest.prop.Checkers

class BakerProtobufSerializerSpec extends TestKit(ActorSystem("BakerProtobufSerializerSpec")) with Checkers with FunSuiteLike {

  val serializer: BakerProtobufSerializer = SerializationExtension.get(system).serializerByIdentity(101).asInstanceOf[BakerProtobufSerializer]

  val ingredientTupleGen: Gen[(String, Value)] = for {
    name <- Gen.alphaNumStr
    data <- Gen.alphaNumStr // this uses akka.remote.serialization.StringSerializer
  } yield (name, PrimitiveValue(data))

  val runtimeEventGen: Gen[RuntimeEvent] = for {
    name <- Gen.alphaNumStr
    ingredient <- Gen.mapOf(ingredientTupleGen)
  } yield RuntimeEvent(name, ingredient.toSeq)

  val processStateGen: Gen[ProcessState] = for {
    name <- Gen.alphaNumStr
    ingredients <- Gen.mapOf(ingredientTupleGen)
    eventNames <- Gen.listOf(Gen.alphaNumStr)
  } yield ProcessState(name, ingredients, eventNames)

  val bakerObjectGen: Gen[Object] = Gen.oneOf(runtimeEventGen, processStateGen)

  test("baker can serialize/deserialize RuntimeEvent and ProcessState classes") {
    val prop = forAll(bakerObjectGen) { (bakerObject) =>
      val bytes = serializer.toBinary(bakerObject)
      val deserializedBakerObject = serializer.fromBinary(bytes, serializer.manifest(bakerObject))
      bakerObject === deserializedBakerObject
    }

    check(prop, Test.Parameters.defaultVerbose.withMinSuccessfulTests(1000))
  }

}
